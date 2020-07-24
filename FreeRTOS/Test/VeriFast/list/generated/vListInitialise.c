void vListInitialise( List_t * const pxList )
    //@ requires List_t_uninitialised(pxList); 
    //@ ensures List_t(pxList, 0, ?end, end, cons(end,nil));
{
    //@ open List_t_uninitialised(pxList);
    
    /* The list structure contains a list item which is used to mark the
     * end of the list.  To initialise the list the list end is inserted
     * as the only list entry. */
    pxList->pxIndex = ( ListItem_t * ) &( pxList->xListEnd ); /*lint !e826 !e740 !e9087 The mini list structure is used as the list end to save RAM.  This is checked and valid. */

    //@ assert ListItem_t(?end, _, _, _, _);
    //@ open ListItem_t(end, _, _, _, _);
    
    /* The list end value is the highest possible value in the list to
     * ensure it remains at the end of the list. */
    pxList->xListEnd.xItemValue = portMAX_DELAY;

    /* The list end next and previous pointers point to itself so we know
     * when the list is empty. */
    pxList->xListEnd.pxNext = ( ListItem_t * ) &( pxList->xListEnd );     /*lint !e826 !e740 !e9087 The mini list structure is used as the list end to save RAM.  This is checked and valid. */
    pxList->xListEnd.pxPrevious = ( ListItem_t * ) &( pxList->xListEnd ); /*lint !e826 !e740 !e9087 The mini list structure is used as the list end to save RAM.  This is checked and valid. */

    pxList->uxNumberOfItems = ( UBaseType_t ) 0U;

    /* Write known values into the list if
     * configUSE_LIST_DATA_INTEGRITY_CHECK_BYTES is set to 1. */
    listSET_LIST_INTEGRITY_CHECK_1_VALUE( pxList );
    listSET_LIST_INTEGRITY_CHECK_2_VALUE( pxList );
    
    //@ close ListItem_t(end, portMAX_DELAY, end, end, _);
    //@ close DLS(end, end, end, end, cons(end,nil), pxList);
    //@ close List_t(pxList, 0, end, end, cons(end,nil));
}

