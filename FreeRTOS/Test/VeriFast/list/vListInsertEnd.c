/*
 * FreeRTOS VeriFast Proofs
 * Copyright (C) Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

#include "proof/list.h"

void vListInsertEnd( List_t * const pxList,
                     ListItem_t * const pxNewListItem )
    //@ requires List_t(pxList, ?len, ?idx, ?end, ?cells) &*& ListItem_t(pxNewListItem, ?val, _, _, _) &*& (mem(pxNewListItem, cells) == false);
    //@ ensures List_t(pxList, len+1, idx, end, ?newcells) &*& (remove(pxNewListItem, newcells) == cells);
{
    //@ open List_t(pxList, len, idx, end, cells);
    //@ assert DLS(end, ?endprev, end, endprev, cells, _);

#ifdef VERIFAST /*< const pointer declaration */    
    ListItem_t * pxIndex = pxList->pxIndex;
#else
    ListItem_t * const pxIndex = pxList->pxIndex;
#endif

    /* Only effective when configASSERT() is also defined, these tests may catch
     * the list data structures being overwritten in memory.  They will not catch
     * data errors caused by incorrect configuration or use of FreeRTOS. */
    listTEST_LIST_INTEGRITY( pxList );
    listTEST_LIST_ITEM_INTEGRITY( pxNewListItem );

    //@ open ListItem_t(pxNewListItem, val, _, _, _);
    
    /*@ 
    
    if (idx == end)
    {
    	open DLS(end, endprev, end, endprev, cells, _);

    	open ListItem_t(end, _, ?endnext, endprev, _);
    	
    	if (end != endprev)
    	{
    	    DLS_length_positive(endnext, endprev);
    	    
    	    if (endprev == endnext)
    	    {
    	        open DLS(endnext, end, end, endprev, tail(cells), _);
    	        open ListItem_t(endprev, _, end, end, _);
    	        
    	    } 
            else
    	    {
    	        DLS_extract_last_item(endnext, endprev, tail(cells));
    	        open ListItem_t(endprev, _, end, _, _);
    	    }
    	}
    	
    } 
    else
    {
    	split_DLS(end, endprev, end, endprev, idx, cells);
    	assert DLS(end, endprev, idx, ?idxprev, ?cells1, _);
    	assert DLS(idx, idxprev, end, endprev, ?cells2, _);
    	index_of_nth(idx, cells);
    	drop_n_plus_one(index_of(idx, cells), cells);
    	append_take_drop_n(cells,index_of(idx,cells));
    	length_append(cells1, cells2);
    	open DLS(idx, idxprev, end, endprev, cells2, _);
    	
    	if (end == idxprev)
    	{
    	    open DLS(end, endprev, idx, idxprev, cells1, _);
    	    
    	} 
        else
    	{
    	    DLS_extract_last_item(end, idxprev, cells1);
	}
    	
    	open ListItem_t(idx, _, _, idxprev, _);
    	open ListItem_t(idxprev, _, idx, _, _);
    	
    }
    
    @*/

    /* Insert a new list item into pxList, but rather than sort the list,
     * makes the new list item the last item to be removed by a call to
     * listGET_OWNER_OF_NEXT_ENTRY(). */
    pxNewListItem->pxNext = pxIndex;
    pxNewListItem->pxPrevious = pxIndex->pxPrevious;

    /* Only used during decision coverage testing. */
    mtCOVERAGE_TEST_DELAY();

    pxIndex->pxPrevious->pxNext = pxNewListItem;
    pxIndex->pxPrevious = pxNewListItem;

    /* Remember which list the item is in. */
    pxNewListItem->pxContainer = pxList;

    ( pxList->uxNumberOfItems )++;
    
    //@ close ListItem_t(pxNewListItem, val, idx, ?idxprev, _);
    
    /*@
    
    if (idx == end)
    {
        close ListItem_t(end, _, ?endnext, pxNewListItem, _);
        close DLS(pxNewListItem, endprev, end, pxNewListItem, cons(pxNewListItem,nil), _);
    	
    	if (end != endprev)
    	{
    	
    	    close ListItem_t(endprev, _, pxNewListItem, _, _);
    	    
    	    if (endprev == endnext)
    	    {
    	        close DLS(endnext, end, end, pxNewListItem, cons(endprev, cons(pxNewListItem, nil)), _);
    	        
    	    } 
            else
    	    {
    	    	close DLS(endprev, ?endprevprev, end, pxNewListItem, cons(endprev, cons(pxNewListItem, nil)), _);
    	    	assert DLS(endnext, end, endprev, endprevprev, ?cells0, _);
    	    	length_take(length(tail(cells)) - 1, tail(cells));
    	    	append_DLS(endnext, end, endprev, endprevprev, end, pxNewListItem, cells0, cons(endprev, cons(pxNewListItem, nil)));
    	    	append_assoc(cells0, cons(endprev, nil), cons(pxNewListItem, nil));
    	    }
    	    
    	    assert DLS(endnext, end, end, pxNewListItem, ?cells0, _);
    	    close DLS(end, pxNewListItem, end, pxNewListItem, cons(end, cells0), _);
    	    close List_t(pxList, len+1, idx, end, cons(end,cells0));
    	    remove_append(pxNewListItem, tail(cells), cons(pxNewListItem,nil));
    	    
    	} 
        else
    	{
    	    close DLS(end, pxNewListItem, end, pxNewListItem, cons(end, cons(pxNewListItem,nil)), _);
    	    close List_t(pxList, len+1, idx, end, cons(end, cons(pxNewListItem,nil)));
    	}
    	
    } 
    else
    {
    	close ListItem_t(idx, _, _, pxNewListItem, _);
    	close ListItem_t(idxprev, _, pxNewListItem, _, _);
    
        if(end == idxprev)
        {
            close DLS(end, endprev, pxNewListItem, idxprev, cons(end, nil), _);
            
        } 
        else
        {
            assert DLS(end, endprev, idxprev, ?idxprevprev, ?cells0, _);
            close DLS(idxprev, idxprevprev, pxNewListItem, idxprev, cons(idxprev, nil), _);
            append_DLS(end, endprev, idxprev, idxprevprev, pxNewListItem, idxprev, cells0, cons(idxprev, nil));
            append_take_drop_n(take(index_of(idx, cells), cells), length(take(index_of(idx, cells), cells)) - 1);
            head_take(idx, cells);
        }
        
        if (idx == endprev)
        {
             close DLS(idx, pxNewListItem, end, endprev, cons(endprev, nil), _);
             
        } 
        else
        {
             assert DLS(_, idx, end, endprev, ?cells0, _);
             close DLS(idx, pxNewListItem, end, endprev, cons(idx,cells0), _);
        }
        
        assert DLS(end, endprev, pxNewListItem, idxprev, ?cells1, _);
        assert DLS(idx, pxNewListItem, end, endprev, ?cells2, _);
        DLS_star_item(idx, endprev, pxNewListItem);
        last_element_in_DLS(idx, endprev, cells2);
        close DLS(pxNewListItem, idxprev, end, endprev, cons(pxNewListItem, cells2), _);
        append_DLS(end, endprev, pxNewListItem, idxprev, end, endprev, cells1, cons(pxNewListItem, cells2));
        length_append(cells1, cons(pxNewListItem, cells2));
        head_append(cells1, cons(pxNewListItem, cells2));
        close List_t(pxList, len+1, idx, end, append(cells1, cons(pxNewListItem, cells2)));
        remove_append(pxNewListItem, cells1, cons(pxNewListItem, cells2)); 
    }
    
    @*/
}