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
    //@ ensures List_t(pxList, len+1, idx, end, _);
{
    //@ open List_t(pxList, len, idx, end, cells);
    //@ assert DLS(end, ?endprev, end, endprev, cells);
    
    ListItem_t * pxIndex = pxList->pxIndex; // Should be ListItem_t * const pxIndex...

    listTEST_LIST_INTEGRITY( pxList );
    listTEST_LIST_ITEM_INTEGRITY( pxNewListItem );

    //@ open ListItem_t(pxNewListItem, val, _, _, _);
    
    /*@ 
    
    if (idx == end)
    {
    	open DLS(end, endprev, end, endprev, cells);

    	open ListItem_t(end, _, ?endnext, endprev, _);
    	
    	if (end != endprev)
    	{
    	    dls_length(endnext, end, end, endprev, tail(cells));
    	    
    	    if (endprev == endnext)
    	    {
    	        open DLS(endnext, end, end, endprev, tail(cells));
    	        open ListItem_t(endprev, _, end, end, _);
    	        
    	    } else
    	    {
    	        extract_last_item(endnext, endprev, tail(cells));
    	        open ListItem_t(endprev, _, end, _, _);
    	    }
    	}
    	
    } else
    {
    	split_dls(end, endprev, end, endprev, idx, cells);
    	assert DLS(end, endprev, idx, ?idxprev, ?cells1);
    	assert DLS(idx, idxprev, end, endprev, ?cells2);
    	
    	index_of_nth(idx, cells);
    	drop_n_plus_one(index_of(idx, cells), cells);
    	append_take_drop_n(cells,index_of(idx,cells));
    	length_append(cells1, cells2);
    	
    	open DLS(idx, idxprev, end, endprev, cells2);
    	
    	if (end == idxprev)
    	{
    	    open DLS(end, endprev, idx, idxprev, cells1);
    	    
    	} else
    	{
    	    extract_last_item(end, idxprev, cells1);
    	}
    	
    	open ListItem_t(idx, _, _, idxprev, _);
    	open ListItem_t(idxprev, _, idx, _, _);
    	
    }
    
    @*/
    
    pxNewListItem->pxNext = pxIndex;
    pxNewListItem->pxPrevious = pxIndex->pxPrevious;

    mtCOVERAGE_TEST_DELAY();

    pxIndex->pxPrevious->pxNext = pxNewListItem;
    pxIndex->pxPrevious = pxNewListItem;

    pxNewListItem->pxContainer = pxList;

    ( pxList->uxNumberOfItems )++;
    
    //@ close ListItem_t(pxNewListItem, val, idx, ?idxprev, _);
    
    /*@
    
    if (idx == end)
    {
    
        close ListItem_t(end, _, ?endnext, pxNewListItem, _);
        close DLS(pxNewListItem, endprev, end, pxNewListItem, cons(pxNewListItem,nil));
    	
    	if (end != endprev)
    	{
    	
    	    close ListItem_t(endprev, _, pxNewListItem, _, _);
    	    
    	    if (endprev == endnext)
    	    {
    	        
    	        close DLS(endnext, end, end, pxNewListItem, cons(endprev, cons(pxNewListItem, nil)));
    	        
    	    } else
    	    {
    	    	close DLS(endprev, ?endprevprev, end, pxNewListItem, cons(endprev, cons(pxNewListItem, nil)));
    	    	assert DLS(endnext, end, endprev, endprevprev, ?cells0);

    	    	length_take(length(tail(cells)) - 1, tail(cells));

    	    	append_dls(endnext, end, endprev, endprevprev, end, pxNewListItem, cells0, cons(endprev, cons(pxNewListItem, nil)));

    	    }
    	    
    	    assert DLS(endnext, end, end, pxNewListItem, ?cells0);
    	    close DLS(end, pxNewListItem, end, pxNewListItem, cons(end, cells0));
    	    close List_t(pxList, len+1, idx, end, cons(end,cells0));
    	    
    	} else
    	{
    	    close DLS(end, pxNewListItem, end, pxNewListItem, cons(end, cons(pxNewListItem,nil)));
    	    close List_t(pxList, len+1, idx, end, cons(end, cons(pxNewListItem,nil)));
    	}
    	
    } else
    {
    
    	close ListItem_t(idx, _, _, pxNewListItem, _);
    	close ListItem_t(idxprev, _, pxNewListItem, _, _);
    
        if(end == idxprev)
        {
        
            close DLS(end, endprev, pxNewListItem, idxprev, cons(end, nil));
            
        } else
        {
            assert DLS(end, endprev, idxprev, ?idxprevprev, ?cells0);
            close DLS(idxprev, idxprevprev, pxNewListItem, idxprev, cons(idxprev, nil));
            append_dls(end, endprev, idxprev, idxprevprev, pxNewListItem, idxprev, cells0, cons(idxprev, nil));
            
            append_take_drop_n(take(index_of(idx, cells), cells), length(take(index_of(idx, cells), cells)) - 1);
            head_take(idx, cells);
            
        }
        
        if (idx == endprev)
        {
             close DLS(idx, pxNewListItem, end, endprev, cons(endprev, nil));
             
        } else
        {
             
             assert DLS(_, idx, end, endprev, ?cells0);
             close DLS(idx, pxNewListItem, end, endprev, cons(idx,cells0));
             
        }
        
        assert DLS(end, endprev, pxNewListItem, idxprev, ?cells1);
        assert DLS(idx, pxNewListItem, end, endprev, ?cells2);
        
        dls_star_item(idx, endprev, pxNewListItem);
        last_element_in_cells(idx, pxNewListItem, end, endprev, cells2);
        
        close DLS(pxNewListItem, idxprev, end, endprev, cons(pxNewListItem, cells2));
        append_dls(end, endprev, pxNewListItem, idxprev, end, endprev, cells1, cons(pxNewListItem, cells2));
        
        length_append(cells1, cons(pxNewListItem, cells2));
        head_append(cells1, cons(pxNewListItem, cells2));
        close List_t(pxList, len+1, idx, end, append(cells1, cons(pxNewListItem, cells2)));
        
    }
    
    @*/
}
/*-----------------------------------------------------------*/