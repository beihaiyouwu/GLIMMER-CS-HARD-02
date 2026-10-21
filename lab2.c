//头文件
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#define WSIZE       8   // 头部或指针字段的字节数（64 位一个字）
#define DSIZE       16  // 双字大小，块与负载的对齐粒度
#define CHUNKSIZE  (1 << 12)       // 扩展堆时的默认字节数
#define MAX_HEAP   (5 * (1 << 20)) // 模拟堆区上限（5MB）
#define MIN_BLK_SIZE (2 * DSIZE)   // 最小块大小（须容纳 hdr + pred + succ + ftr）

#define ALIGN(size) (((size) + (DSIZE - 1)) & ~(DSIZE - 1)) // 向上对齐到 DSIZE 的倍数

#define MAX(x, y)  ((x) > (y) ? (x) : (y))  // 返回较大值


#define PACK(size, prev_alloc, alloc) \
    (((size) & ~0x7) | ((prev_alloc) << 1) | (alloc))  // 将 size、前块分配位、本块分配位合并为一个字
#define PACK_PREV_ALLOC(val, prev_alloc) (((val) & ~0x2) | ((prev_alloc) << 1))  // 只更新 header 中的 prev_alloc 位
#define PACK_ALLOC(val, alloc) (((val) & ~0x1) | (alloc))  // 只更新 header 中的 alloc 位

#define GET(p)        (*(unsigned long *)(p))  // 读地址 p 处的一个字
#define PUT(p, val)   (*(unsigned long *)(p) = (val))  // 向地址 p 处写一个字

#define GET_SIZE(p)       (GET(p) & ~0x7)           // 从 header/footer 取出块大小
#define GET_ALLOC(p)      (GET(p) & 0x1)            // 本块是否已分配
#define GET_PREV_ALLOC(p) ((GET(p) >> 1) & 0x1)     // 物理上前一块是否已分配（已分配块可无 footer）

#define HDRP(bp)  ((char *)(bp) - WSIZE)  // 块头部指针（bp 为有效荷载起始地址）
#define FTRP(bp)  ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)  // 块尾部指针（主要用于空闲块）

#define GET_PRED(bp)  ((char *)GET(bp))  // 空闲块负载处：前驱空闲块指针
#define SET_PRED(bp, val)  (PUT(bp, (unsigned long)(val)))
#define GET_SUCC(bp)  ((char *)GET((char *)(bp) + WSIZE))  // 空闲块负载 +8：后继空闲块指针
#define SET_SUCC(bp, val)  (PUT((char *)(bp) + WSIZE, (unsigned long)(val)))

#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))  // 下一块的有效荷载指针
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))  // 前一块的有效荷载指针（经前块 footer）

static char *heap_listp;      // 序言块有效荷载地址，物理堆遍历起点
static char *free_listp;      // 显式空闲链表表头
static char *mem_start_brk;   // 向 OS 预留的堆区起始地址
static char *mem_brk;         // 当前堆顶（mm_sbrk 在此基础上递增）
static char *mem_max_addr;    // 堆区上界（mem_start_brk + MAX_HEAP）

#ifdef DEBUG
#define VERBOSE 1  // 在调试模式下启用调试信息输出
#else
#define VERBOSE 0  // 默认不输出调试信息
#endif
//函数声明
static void print_heap_blocks(int verbose, const char* func);
int mm_init(void);
void *mm_sbrk(int incr);
static void *find_fit_first(size_t asize);
static void *extend_heap(size_t words);
static void *find_fit_best(size_t asize);
static void place(void* bp, size_t asize);
static void* coalesce(void* bp);
static void delete_from_free_list(void *bp);
static void add_to_free_list(void *bp);
void *mm_malloc(size_t size);
void mm_free(void *bp);
void *mm_realloc(void *ptr, size_t size);
//同part1的调试模式
static void print_heap_blocks(int verbose, const char* func) {
    if (verbose) {
        char *curbp = (char *)NEXT_BLKP(heap_listp);
        printf("\n=========================== %s ===========================\n", func);

        while (GET_SIZE(HDRP(curbp)) > 0) {
            printf("Address: %p\n", curbp);
            printf("Size: %lu\n", GET_SIZE(HDRP(curbp)));
            printf("Allocated: %lu\n", GET_ALLOC(HDRP(curbp)));
            printf("\n");
            curbp = NEXT_BLKP(curbp);
        }

        printf("Address: %p\n", curbp); // Should point to the end of the heap
        printf("Size: 0\n");
        printf("Allocated: 1\n");
        printf("=========================== %s ===========================\n", func);
    }
}

/**
 * @brief 初始化内存分配器。
 *
 * 实现上文堆的衍生方式中指定的初始化，初始化全局变量，分好堆1堆2
 */
int mm_init(void)
{
    mem_start_brk=(char*)malloc(MAX_HEAP);//初始堆得到开始的地址
    mem_brk = mem_start_brk; //初始当前的堆顶
    mem_max_addr = mem_start_brk + MAX_HEAP;//初始堆的上界

    // 2. 初始化空闲链表头
    free_listp=NULL;

    char *p=(char *)mm_sbrk(4*WSIZE);
    if (p==(void*)-1) 
    {
        return -1; // 申请失败
    }
    //初始化序言块
    PUT(p,1);                              
    PUT(p +(1*WSIZE),PACK(DSIZE,1,1)); //首
    PUT(p + (2*WSIZE), PACK(DSIZE,1,1));//尾
    PUT(p + (3*WSIZE), PACK(0,1,1)); //初始化尾块用来标记    
    heap_listp=p+DSIZE;//开头
    char *bp=extend_heap(4);//分配内存
    if (bp==NULL) //分配失败
    {
        return -1;
    }

    return 0;
}

/**
 * @brief 增加程序的数据空间。
 *
 * @param incr 要增加的字节数。
 *
 * @return 扩展后的内存起始地址；如果扩展失败，则返回 (void *)-1。
 *
 * 实现上文堆的衍生方式中的功能
 */
void *mm_sbrk(int incr)
{
 void*old=mem_brk;//旧地址
 if(incr==0)
 {
    return mem_start_brk;
 }
 if(incr<0)
 {
 return (void*)-1;
 }
if((mem_brk+incr)>mem_max_addr)//超出边界
{
    return (void*)-1;
}
mem_brk=(char*)mem_brk+incr;//更新堆顶
return old;//返回旧的地址，也就是内存起始的地址
}


/**
 * @brief 扩展堆空间。
 *
 * @param words 要扩展的字数。
 *
 * @return 返回新扩展区域的起始地址；如果扩展失败，则返回 NULL。
 *
 * extend_heap函数是对mem_sbrk的一层封装，接收的参数是要分配的字数
 * 在堆初始化以及malloc找不到合适内存块时使用
 * 它首先对请求大小进行地址对齐，然后调用mem_sbrk获取空间
 */
static void *extend_heap(size_t words)
{
    words=(words%2)?(words+1):words;//传入的字初始化为偶数
    size_t size=words*WSIZE;//算出字节数
    void *bp=mm_sbrk(size);//得到旧地址
    if(bp==(void*)-1)//分配失败
    {
        perror("sbrk 失败");
        return NULL;
    }
    PUT(HDRP(bp),PACK(size,1,1));//头部元信息
    PUT(FTRP(bp),PACK(size,1,1));//尾部元信息
    PUT(HDRP(NEXT_BLKP(bp)),PACK(0,0,1));//尾声块
    return coalesce(bp);//合并
}

/**
 * @brief 查找适合分配的空闲块（首次适应）。
 *
 * @param asize 请求的块大小（以字节为单位）。
 *
 * @return 返回找到的适合的空闲块的指针；如果没有找到合适的空闲块，则返回 NULL。
 *
 * 该函数在空闲链表中查找第一个合适的块，以满足请求的大小。
 */
static void *find_fit_first(size_t asize)
{
    void *bp=free_listp;//从头开始
    while(bp!=NULL)
    {
        if(GET_ALLOC(HDRP(bp))==0&&GET_SIZE(HDRP(bp))>=asize)//符合条件
        {
            return bp;
        }
        bp=GET_SUCC(bp);//指针往后，实现遍历
    }
    return NULL;//没有找到返回NULL
}

//类似find_fit_first
static void *find_fit_best(size_t asize)//寻找最适合的，即遍历完所有找符合条件最小的
{
    void *bp=free_listp;
    void *min=bp;
    while(bp!=NULL)
    {
        if(GET_ALLOC(HDRP(bp))==0&&GET_SIZE(HDRP(bp))>=asize)
        {
            if(GET_SIZE(HDRP(min))>GET_SIZE(HDRP(bp)))//更新最小的块
            {
                min=bp;
            }
        }
        bp=GET_SUCC(bp);//往后
    }
    if(bp==NULL)//没有找到
    {
        return NULL;
    }
    else
    {
        return min;//返回最小的
    }
}

/**
 * @brief 将指定的块放置到分配状态。
 *
 * @param bp 要分配的块的起始地址。
 * @param asize 请求的块大小（以字节为单位）。
 *
 * 该函数将指定的块标记为已分配，并更新块的大小信息。
 */
static void place(void* bp, size_t asize)//个人感觉最难的一部分
{
    if (bp == NULL) 
    {
    return;
    }
    size_t csize=GET_SIZE(HDRP(bp));//得到空闲块的大小
    delete_from_free_list(bp);//先从空链表中拿出来
    if((csize-asize)>=MIN_BLK_SIZE)//符合条件 
    {
        size_t prev_alloc = GET_PREV_ALLOC(HDRP(bp));
        //1.分配前半块
        PUT(HDRP(bp),PACK(asize,prev_alloc,1));
        PUT(FTRP(bp),PACK(asize,prev_alloc,1)); 
        //2.构造后半块
        char *next_bp=NEXT_BLKP(bp);
        size_t remain_size=csize-asize;  
        PUT(HDRP(next_bp),PACK(remain_size,1,0)); 
        PUT(FTRP(next_bp),PACK(remain_size,1,0)); 
        char *next_next=NEXT_BLKP(next_bp);
        PUT(HDRP(next_next),PACK_PREV_ALLOC(GET(HDRP(next_next)),0)); 
        add_to_free_list(next_bp);//把剩下空闲的加回去 
    } 
    else
    {
        //剩余空间太小,整块分配
        size_t prev_alloc=GET_PREV_ALLOC(HDRP(bp));
        PUT(HDRP(bp),PACK(csize,prev_alloc,1));
        PUT(FTRP(bp),PACK(csize,prev_alloc,1)); 
        //同步下一块的prev_alloc=1
        char *next_bp=NEXT_BLKP(bp);
        PUT(HDRP(next_bp),PACK_PREV_ALLOC(GET(HDRP(next_bp)),1));
    }
}

/**
 * @brief 合并相邻的空闲块。
 *
 * @param bp 要合并的块的起始地址。
 *
 * @return 合并后的块的起始地址。
 *
 * 该函数合并当前块与其相邻的空闲块，以减少内存碎片并增加大块的可用内存。
 */
static void* coalesce(void* bp)//与隐式写法大部分一样
{
     delete_from_free_list(bp);//从空闲链表中拿出去
     size_t size=GET_SIZE(HDRP(bp));//当前块的大小
     if(GET_PREV_ALLOC(HDRP(bp))==1&&GET_ALLOC(HDRP(NEXT_BLKP(bp)))==1)//前面后面的块都分配了
     {
        add_to_free_list(bp);
        return bp;//不合并
     }
     if(GET_PREV_ALLOC(HDRP(bp))==0&&GET_ALLOC(HDRP(NEXT_BLKP(bp)))==1)//前未分配后被分配
     {
        void *pre=PREV_BLKP(bp);//指向前面的块
        delete_from_free_list(pre);
        size+=GET_SIZE(HDRP(pre));//算总的大小
        PUT(HDRP(pre),PACK(size,1,0));//合并更新大小
        PUT(FTRP(pre),PACK(size,1,0));
        char *next_next = NEXT_BLKP(pre);//更新后面一个块的PREV_ALLOC情况
        PUT(HDRP(next_next), PACK_PREV_ALLOC(GET_SIZE(HDRP(next_next)), 0));
        add_to_free_list(pre);
        return pre;//返回合并后的指针
     }
     if(GET_PREV_ALLOC(HDRP(bp))==1&&GET_ALLOC(HDRP(NEXT_BLKP(bp)))==0)//前分配后未分配
     {
        void *next=NEXT_BLKP(bp);
        delete_from_free_list(next);
        size+=GET_SIZE(HDRP(next));
        PUT(HDRP(bp),PACK(size,1,0));
        PUT(FTRP(bp),PACK(size,1,0));
        char *next_next = NEXT_BLKP(bp);
        PUT(HDRP(next_next), PACK_PREV_ALLOC(GET_SIZE(HDRP(next_next)), 0));
        add_to_free_list(bp);
        return bp;
     }
     if(GET_PREV_ALLOC(HDRP(bp))==0&&GET_ALLOC(HDRP(NEXT_BLKP(bp)))==0)//前后都未分配
     {
        void *pre=PREV_BLKP(bp);
        void *next=NEXT_BLKP(bp);
        delete_from_free_list(pre);
        delete_from_free_list(next);
        size=GET_SIZE(HDRP(pre))+GET_SIZE(HDRP(bp))+GET_SIZE(HDRP(NEXT_BLKP(bp)));//三块总大小
        PUT(HDRP(pre),PACK(size,1,0));//合并形成新的空闲块
        PUT(FTRP(next),PACK(size,1,0));
        char *next_next = NEXT_BLKP(pre);
        PUT(HDRP(next_next), PACK_PREV_ALLOC(GET_SIZE(HDRP(next_next)), 0));
        add_to_free_list(pre);
        return pre;//返回空闲块的头部指针
     }
     
     
}


/**
 * @brief 从空闲链表中移除指定的空闲块。
 *
 * @param bp 要移除的空闲块的起始地址。
 *
 * 该函数将指定的空闲块从空闲链表中移除，以便将其标记为已分配。
 */
static void delete_from_free_list(void *bp)
{
    if(GET_PRED(bp)==NULL)//前边一个为空则自己作为头
    {
        free_listp=GET_SUCC(bp);
    }
    else{
    if(GET_SUCC(bp)==NULL)
    {
       SET_SUCC(GET_PRED(bp),bp);
    }
    else
    {
    SET_SUCC(GET_PRED(bp),GET_SUCC(bp));//自己的前继指向自己的后继
    SET_PRED(GET_SUCC(bp),GET_PRED(bp));//自己的后继指向自己的前继
    }
}
}
/**
 * @brief 将指定的空闲块插入到空闲链表中。
 *
 * @param bp 要插入的空闲块的起始地址。
 *
 * 该函数用头插法将指定的空闲块插入到空闲链表中，以便将其标记为可用的空闲块。
 */
static void add_to_free_list(void *bp)
{
    if(bp==NULL)
    {
        return;
    }
    SET_SUCC(bp,free_listp);//自己的后继为头
    if(free_listp!=NULL)
    {
    SET_PRED(free_listp,bp);//头的后继为自己实现头插
    }
    free_listp=bp;//自己成为新的头
}

/**
 * @brief 分配内存块。
 *
 * @param size 请求的内存块大小（以字节为单位）。该大小包括块头和块尾所需的空间。
 *
 * @return 返回分配的内存块的起始地址；如果分配失败，则返回 NULL。
 *
 * 该函数根据请求的大小在堆中查找适合的空闲块，如果找到合适的块则分配该块，并返回其起始地址。如果没有足够的空间，则可能会扩展堆或返回 NULL。
 */
void *mm_malloc(size_t size)
{
    size_t asize=ALIGN(DSIZE+size);//实际分配大小，还要加上两个指针的大小
    if(asize<MIN_BLK_SIZE)
    {
        asize=MIN_BLK_SIZE;
    }
    void *bp=find_fit_first(asize);//找到一个空闲块
    if(bp==NULL)
    {
        size_t extendsize=MAX(CHUNKSIZE,asize);//新分配内存
        bp=extend_heap(extendsize/WSIZE);
        if(bp==NULL)//分配失败
        {
        return NULL;
        }
    }
    place(bp,asize);//放进空闲块切割（如果需要的话）
    print_heap_blocks(1,"mm_malloc");//调试
    return bp;  
}
/**
 * @brief 释放内存块。
 *
 * @param bp 要释放的内存块的起始地址。
 *
 * 该函数将指定的内存块标记为已释放，并尝试将其合并到相邻的空闲块中，以减少内存碎片。
 */
void mm_free(void *bp)
{
    PUT(HDRP(bp),PACK(GET_SIZE(HDRP(bp)),GET_PREV_ALLOC(HDRP(bp)),0));//标记为空
    PUT(FTRP(bp),PACK(GET_SIZE(HDRP(bp)),GET_PREV_ALLOC(HDRP(bp)),0));
    add_to_free_list(bp);//加入空闲链表
    char *next = NEXT_BLKP(bp);
    PUT(HDRP(next), PACK_PREV_ALLOC(GET(HDRP(next)), 0));//自己的后继的prevalloc也要改一下
    coalesce(bp);//合并
    print_heap_blocks(1,"mm_free");
}

/**
 * @brief 重新分配内存块。
 *
 * @param ptr 指向要重新分配的内存块的起始地址。如果 ptr 为 NULL，则相当于调用 mm_malloc。
 * @param size 请求的新内存块大小（以字节为单位）。该大小包括块头和块尾所需的空间。
 *
 * @return 返回重新分配的内存块的起始地址；如果重新分配失败，则返回 NULL。
 *
 * 该函数调整指定内存块的大小。如果新的大小大于原始大小，会在堆中分配新的内存块，并将原始数据复制到新内存块中。如果新的大小小于原始大小，则会截断原始数据。原始内存块的内容在重新分配之前被保留。
 */
void *mm_realloc(void *ptr, size_t size)
{
    size_t asize=ALIGN(size);
    if(ptr==NULL)
    {
        mm_malloc(asize);//重新分配
    }
    if(asize>GET_SIZE(ptr))
    {
        ptr=mm_malloc(asize);
        return ptr;
    }
    else
    {
        size_t prev_alloc=GET_PREV_ALLOC(HDRP(ptr));
        PUT(HDRP(ptr),PACK(asize,prev_alloc,1));
        PUT(FTRP(ptr),PACK(asize,prev_alloc,1)); 
        char *next_bp=NEXT_BLKP(ptr);
        size_t remain_size=GET_SIZE(ptr)-size; 
        PUT(HDRP(next_bp),PACK(remain_size,1,0)); 
        PUT(FTRP(next_bp),PACK(remain_size,1,0)); 
        add_to_free_list(next_bp);//加到空闲链表
    }
}
//测试用例
int main() {
    if (mm_init() == -1) {
        printf("Memory manager initialization failed.\n");
        return -1;
    }

    void *p1 = mm_malloc(8000);
    void *p2 = mm_malloc(200);
    void *p3 = mm_malloc(50);

    mm_free(p2);

    void *p4 = mm_malloc(150);

    mm_free(p1);
    mm_free(p3);
    mm_free(p4);

    return 0;
}