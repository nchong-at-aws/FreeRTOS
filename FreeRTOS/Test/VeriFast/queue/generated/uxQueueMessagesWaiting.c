UBaseType_t uxQueueMessagesWaiting( const QueueHandle_t xQueue )
/*@requires [1/2]queuehandle(xQueue, ?N, ?M, ?is_isr) &*& is_isr == false;@*/
/*@ensures [1/2]queuehandle(xQueue, N, M, is_isr);@*/
{
    UBaseType_t uxReturn;

    configASSERT( xQueue );

    taskENTER_CRITICAL();
    {
        /*@assert queue(xQueue, ?Storage, N, M, ?W, ?R, ?K, ?is_locked, ?abs);@*/
        uxReturn = ( ( Queue_t * ) xQueue )->uxMessagesWaiting;
        /*@close queue(xQueue, Storage, N, M, W, R, K, is_locked, abs);@*/
    }
    taskEXIT_CRITICAL();

    return uxReturn;
} /*lint !e818 Pointer cannot be declared const as xQueue is a typedef not pointer. */

