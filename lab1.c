
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>

/* ==================== 常量与对齐宏 ==================== */
#define ALIGNMENT 8  // 双字对齐
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~(ALIGNMENT-1)) // 对齐到ALIGNMENT的倍数

#define WSIZE       4  // 头部或尾部的字节数
#define DSIZE       8  // 双字大小
#define CHUNKSIZE  (1<<12)  // 扩展堆时的默认大小
#define MINBLOCK (DSIZE + 2*WSIZE)  // 最小块大小

#define MAX(x, y)  ((x) > (y) ? (x) : (y))  // 返回最大值

/* ==================== 读写块字段的宏 ==================== */
#define PACK(size, alloc)  ((size) | (alloc))  // 将 size 和 allocated bit 合并为一个字

#define GET(p)        (*(unsigned int *)(p))  // 读地址p处的一个字
#define PUT(p, val)   (*(unsigned int *)(p) = (val))  // 向地址p处写一个字

#define GET_SIZE(p)   (GET(p) & ~0x07)  // 获取块的大小
#define GET_ALLOC(p)  (GET(p) & 0x1)  // 获取分配标志

#define HDRP(bp)     ((char*)(bp) - WSIZE)  // 获取头部指针(bp是一个块的有效荷载的起始地址)
#define FTRP(bp)     ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)  // 获取尾部指针

#define NEXT_BLKP(bp)    ((char*)(bp) + GET_SIZE((char*)(bp) - WSIZE))  // 获取下一个块的指针
#define PREV_BLKP(bp)    ((char*)(bp) - GET_SIZE((char*)(bp) - DSIZE))  // 获取前一个块的指针

/* ==================== 全局状态 ==================== */
static char *heap_listp;  // 堆的开始指针

#ifdef DEBUG
#define VERBOSE 1  // 在调试模式下启用调试信息输出
#else
#define VERBOSE 0  // 默认不输出调试信息
#endif

/* ==================== 前向声明 ==================== */
static void *extend_heap(size_t size);
static void *find_fit(size_t size);
static void place(char *bp, size_t asize);
static void *coalesce(void *bp);
static void print_heap_blocks(int verbose, const char *func);
/**
 * @brief 初始化内存分配器
 *
 * @return 成功时返回 0，失败时返回 -1
 */
int mm_init(void)
{
    // 初始化堆
    if ((heap_listp = sbrk(4*WSIZE)) == (void*)-1)
        return -1;

    // 初始化空闲链表
    PUT(heap_listp, 0);
    PUT(heap_listp + 1*WSIZE, PACK(8, 1));
    PUT(heap_listp + 2*WSIZE, PACK(8, 1));
    PUT(heap_listp, PACK(0, 1));
    heap_listp += (2*WSIZE);

    // 扩展堆
    if (extend_heap(CHUNKSIZE) == NULL)
        return -1;

    return 0;
}
/**
 * @brief 打印当前堆块的状态信息。
 *
 * 根据传入的 verbose 参数决定是否打印堆块信息。此函数用于调试，
 * 以检查堆内存布局、块大小及其分配状态。
 *
 * @param verbose  控制是否打印输出。当 verbose 为 1 时打印信息，为 0 时不打印。
 * @param func     表示调用此函数的上下文或函数名称，用于输出中标识当前的操作阶段。
 */
static void print_heap_blocks(int verbose, const char* func) {
    if (!verbose) return;  // 如果不需要输出调试信息，则直接返回

    char *curbp = (char *)heap_listp;

    printf("\n=========================== %s ===========================\n", func);

    while (GET_SIZE(HDRP(curbp)) > 0) 
    {
        printf("Address: %p\n", curbp);
        printf("Size: %d\n", GET_SIZE(HDRP(curbp)));
        printf("Allocated: %d\n", GET_ALLOC(HDRP(curbp)));
        printf("\n");
        curbp = NEXT_BLKP(curbp);
    }

    printf("Address: %p\n", curbp); // Should point to the end of the heap
    printf("Size: 0\n");
    printf("Allocated: 1\n");
    printf("=========================== %s ===========================\n", func);
}


/**
 * @brief 扩展堆的大小以适应请求的内存。
 *
 * 这个函数通过调用 sbrk 来扩展堆的大小。扩展的大小会被调整为CHUNKSIZE的整数倍，以便更好地管理堆内存。
 *
 * @param size 需要扩展的内存大小（以字节为单位）。
 *
 * @note 初始调用mm_init时扩展一个CHUNKSIZE
 * @return 扩展后的内存块的指针，如果扩展失败则返回 NULL。
 */
static void *extend_heap(size_t size) 
{
    void *bp=sbrk(size);//分配内存
    if(bp==(void*)-1)//分配失败
    {
        perror("sbrk 失败");
        return NULL;
    }
    PUT(HDRP(bp),PACK(size,0));//头部元信息
    PUT(FTRP(bp),PACK(size,0));//尾部元信息
    PUT(bp+size,PACK(0,1));//尾声块
    return coalesce(bp);//合并

}


/**
 * @brief 在堆中查找合适的空闲块。
 *
 * 这个函数遍历堆中的所有块，寻找一个大小足够且未分配的空闲块。
 *
 * @param size 需要分配的内存块的大小（以字节为单位）。
 *
 * @return 找到的合适的空闲块的指针，如果没有找到则返回 `NULL`。
 */
static void *find_fit(size_t size) 
{
    if(heap_listp==NULL)
    {
        return NULL;
    }
    void *bp=heap_listp;//将堆开始的指针赋给bp
    while(GET_SIZE(HDRP(bp))>0)//依靠尾声块来判断终止
    {
        if(GET_ALLOC(HDRP(bp))==0&&GET_SIZE(HDRP(bp))>= size)//未分配且大小足够
        {
            return bp;
        }
       bp=NEXT_BLKP(bp);//遍历下一个块
    }
    return NULL;//没有找到返回NULL
}


/**
 * @brief 将内存块分配给用户。
 *
 * 这个函数会根据请求的大小 asize(对齐后的size) 将一个内存块分配给用户。如果分配的块剩余的空间足够大，则将剩余的空间保留为一个新的空闲块。否则，将整个块都分配出去。
 *
 * @param bp 指向要分配的内存块的指针。
 * @param asize 需要分配的内存块的大小（以字节为单位）。
 */
static void place(char *bp, size_t asize) 
{
if(bp==NULL)//分配失败
{
return;
}
if(GET_SIZE(HDRP(bp))>asize&&(GET_SIZE(HDRP(bp))-asize)>=MINBLOCK)//空的块大于需要的
{
    size_t size=GET_SIZE(HDRP(bp))-asize;//算剩下的大小
    PUT(HDRP(bp),PACK(asize,1));//分配要分配的块进行头尾标记
    PUT(FTRP(bp),PACK(asize,1));
    PUT(HDRP(NEXT_BLKP(bp)),PACK(size,0));//剩下的为空闲块
    PUT(FTRP(NEXT_BLKP(bp)),PACK(size,0));
}
else
{
    size_t extersize=MAX(asize,CHUNKSIZE);
    PUT(HDRP(bp),PACK(extersize,1));//内存不够，全部分配
     PUT(FTRP(bp),PACK(extersize,1));
}
}


/**
 * @brief 分配一个指定大小的内存块。
 *
 * 这个函数会根据请求的内存大小size来分配内存。如果请求的大小为零，则返回 NULL。首先，函数尝试从空闲块列表中找到一个合适的块，如果找到，则进行分配。如果没有找到合适的块，则会扩展堆的大小，并再次尝试分配内存。
 *
 * @param size 需要分配的内存大小（以字节为单位）。
 *
 * @return 指向分配的内存块的指针，如果分配失败则返回 `NULL`。
 */
void *mm_malloc(size_t size) 
{
   if(size==0)//大小为0返回NULL
   {
    return NULL;
   }
   size_t asize=ALIGN(size+DSIZE);//必须是8的倍数,还要额外加入头尾存储元信息占用的空间
   void* p=find_fit(asize);//寻找空闲块
   if(p==NULL)//没有找到重新开辟
   {
    p=extend_heap(asize);
    if(p==NULL)//开辟失败
    {
        return NULL;
    }
    }  
    place(p,asize);//在空闲块中分配内存
    print_heap_blocks(1,"mm_malloc");
    return p;
   
}


/**
 * @brief 合并相邻的空闲块。
 *
 * 这个函数检查指定块 bp 的前后相邻块的分配状态。如果相邻的块为空闲块，则将这些块合并成一个更大的空闲块，并更新其头部和尾部。函数会返回合并后的空闲块的指针。
 *
 * @param bp 指向要进行合并操作的内存块的指针。
 *
 * @return 合并后的空闲块的指针。
 */
static void *coalesce(void *bp) 
{
     size_t size=GET_SIZE(HDRP(bp));//当前块的大小
     if(GET_ALLOC(HDRP(PREV_BLKP(bp)))==1&&GET_ALLOC(HDRP(NEXT_BLKP(bp)))==1)//前面后面的块都分配了
     {
        return bp;//不合并
     }
     if(GET_ALLOC(HDRP(PREV_BLKP(bp)))==0&&GET_ALLOC(HDRP(NEXT_BLKP(bp)))==1)//前未分配后被分配
     {
        void *pre=PREV_BLKP(bp);//指向前面的块
        size+=GET_SIZE(HDRP(pre));//算总的大小
        PUT(HDRP(pre),PACK(size,0));//合并更新大小
        PUT(FTRP(pre),PACK(size,0));
        return pre;//返回合并后的指针
     }
     if(GET_ALLOC(HDRP(PREV_BLKP(bp)))==1&&GET_ALLOC(HDRP(NEXT_BLKP(bp)))==0)//前分配后未分配
     {
        void *next=NEXT_BLKP(bp);
        size+=GET_SIZE(HDRP(next));
        PUT(HDRP(bp),PACK(size,0));
        PUT(FTRP(bp),PACK(size,0));
        return bp;
     }
     if(GET_ALLOC(HDRP(PREV_BLKP(bp)))==0&&GET_ALLOC(HDRP(NEXT_BLKP(bp)))==0)//前后都未分配
     {
        void *pre=PREV_BLKP(bp);
        void *next=NEXT_BLKP(bp);
        size=GET_SIZE(HDRP(pre))+GET_SIZE(HDRP(bp))+GET_SIZE(HDRP(NEXT_BLKP(bp)));//三块总大小
        PUT(HDRP(pre),PACK(size,0));//合并形成新的空闲块
        PUT(FTRP(next),PACK(size,0));
        
        return pre;//返回空闲块的头部指针
     }
     
     
}


/**
 * @brief 释放一个已分配的内存块。
 *
 * 这个函数将指定的内存块 ptr 标记为未分配，并尝试将其与相邻的空闲块合并。
 *
 * @param ptr 指向要释放的内存块的指针。
 */
void mm_free(void *ptr)
 {
    PUT(HDRP(ptr),PACK(GET_SIZE(HDRP(ptr)),0));//标记为空闲块
    PUT(FTRP(ptr),PACK(GET_SIZE(HDRP(ptr)),0));
    coalesce(ptr);//合并
      print_heap_blocks(1,"mm_free");
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