static void prvInitialiseNewQueue( const UBaseType_t uxQueueLength,
                                   const UBaseType_t uxItemSize,
                                   uint8_t * pucQueueStorage,
                                   const uint8_t ucQueueType,
                                   Queue_t * pxNewQueue )

/*@requires queue_init1(pxNewQueue) &*&
    0 < uxQueueLength &*& 0 < uxItemSize &*&
    malloc_block(pucQueueStorage, uxQueueLength * uxItemSize) &*&
    pucQueueStorage + uxQueueLength * uxItemSize <= (uint8_t *)UINTPTR_MAX &*&
    uchars(pucQueueStorage, uxQueueLength * uxItemSize,_);@*/
/*@ensures queue(pxNewQueue, ((int8_t *)(void *)pucQueueStorage), uxQueueLength, uxItemSize, 0, (uxQueueLength-1), 0, false, nil) &*&
    queuelists(pxNewQueue);@*/
{
#ifndef VERIFAST /*< void cast of unused var */
    /* Remove compiler warnings about unused parameters should
     * configUSE_TRACE_FACILITY not be set to 1. */
    ( void ) ucQueueType;
#endif

    if( uxItemSize == ( UBaseType_t ) 0 )
    {
        /* No RAM was allocated for the queue storage area, but PC head cannot
         * be set to NULL because NULL is used as a key to say the queue is used as
         * a mutex.  Therefore just set pcHead to point to the queue as a benign
         * value that is known to be within the memory map. */
#ifdef VERIFAST /*< stricter casting */
        pxNewQueue->pcHead = ( int8_t * ) ( void * ) pxNewQueue;
#else
        pxNewQueue->pcHead = ( int8_t * ) pxNewQueue;
#endif
    }
    else
    {
        /* Set the head to the start of the queue storage area. */
#ifdef VERIFAST /*< stricter casting */
        pxNewQueue->pcHead = ( int8_t * ) ( void * ) pucQueueStorage;
#else
        pxNewQueue->pcHead = ( int8_t * ) pucQueueStorage;
#endif
    }

    /* Initialise the queue members as described where the queue type is
     * defined. */
    pxNewQueue->uxLength = uxQueueLength;
    pxNewQueue->uxItemSize = uxItemSize;
    /*@close queue_init2(pxNewQueue, _, uxQueueLength, uxItemSize);@*/
#ifdef VERIFAST /*< void cast of unused return value */
    xQueueGenericReset( pxNewQueue, pdTRUE );
#else
    ( void ) xQueueGenericReset( pxNewQueue, pdTRUE );
#endif

    #if ( configUSE_TRACE_FACILITY == 1 )
        {
            pxNewQueue->ucQueueType = ucQueueType;
        }
    #endif /* configUSE_TRACE_FACILITY */

    #if ( configUSE_QUEUE_SETS == 1 )
        {
            pxNewQueue->pxQueueSetContainer = NULL;
        }
    #endif /* configUSE_QUEUE_SETS */

    traceQUEUE_CREATE( pxNewQueue );
}

