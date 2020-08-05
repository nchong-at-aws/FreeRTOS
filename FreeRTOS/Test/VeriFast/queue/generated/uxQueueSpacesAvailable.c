UBaseType_t uxQueueSpacesAvailable( const QueueHandle_t xQueue )
/*@requires [1/2]queuehandle(xQueue, ?N, ?M, ?is_isr) &*& is_isr == false;@*/
/*@ensures [1/2]queuehandle(xQueue, N, M, is_isr);@*/
{
    UBaseType_t uxReturn;

#ifdef VERIFAST /*< const pointer declaration */
    Queue_t * pxQueue = xQueue;
#else
    Queue_t * const pxQueue = xQueue;
#endif

    configASSERT( pxQueue );

    taskENTER_CRITICAL();
    /*@assert queue(xQueue, ?Storage, N, M, ?W, ?R, ?K, ?is_locked, ?abs);@*/
    {
        uxReturn = pxQueue->uxLength - pxQueue->uxMessagesWaiting;
        /*@assert uxReturn == N - K;@*/
    }
    /*@close queue(xQueue, Storage, N, M, W, R, K, is_locked, abs);@*/
    taskEXIT_CRITICAL();

    return uxReturn;
} /*lint !e818 Pointer cannot be declared const as xQueue is a typedef not pointer. */

