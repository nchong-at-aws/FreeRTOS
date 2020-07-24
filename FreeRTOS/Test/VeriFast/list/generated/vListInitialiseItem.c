void vListInitialiseItem( ListItem_t * const pxItem )
    //@ requires ListItem_t(pxItem, ?value, ?next, ?prev, _);
    //@ ensures ListItem_t(pxItem, value, next, prev, NULL);
{

    //@ open ListItem_t(pxItem, value, next, prev, _);
    
    /* Make sure the list item is not recorded as being on a list. */
    pxItem->pxContainer = NULL;

    /* Write known values into the list item if
     * configUSE_LIST_DATA_INTEGRITY_CHECK_BYTES is set to 1. */
    listSET_FIRST_LIST_ITEM_INTEGRITY_CHECK_VALUE( pxItem );
    listSET_SECOND_LIST_ITEM_INTEGRITY_CHECK_VALUE( pxItem );
    
    //@ close ListItem_t(pxItem, value, next, prev, NULL);
}

