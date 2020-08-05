BaseType_t xQueueIsQueueFullFromISR( const QueueHandle_t xQueue )
/*@requires queue(xQueue, ?Storage, ?N, ?M, ?W, ?R, ?K, ?is_locked, ?abs);@*/
/*@ensures queue(xQueue, Storage, N, M, W, R, K, is_locked, abs) &*&
    result == ((K == N) ? pdTRUE : pdFALSE);@*/
{
    BaseType_t xReturn;

#ifdef VERIFAST /*< const pointer declaration */
    Queue_t * pxQueue = xQueue;
#else
    Queue_t * const pxQueue = xQueue;
#endif

    configASSERT( pxQueue );

    if( pxQueue->uxMessagesWaiting == pxQueue->uxLength )
    {
        xReturn = pdTRUE;
    }
    else
    {
        xReturn = pdFALSE;
    }

    return xReturn;
} /*lint !e818 xQueue could not be pointer to const because it is a typedef. */

