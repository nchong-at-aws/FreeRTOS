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

UBaseType_t uxListRemove( ListItem_t * const pxItemToRemove )
    //@ requires exists<struct xLIST *>(?container) &*& List_t(container, ?len, ?idx, ?end, ?cells) &*& (mem(pxItemToRemove, cells) == true) &*& (pxItemToRemove != end);
    //@ ensures List_t(container, len-1, _, end, remove(pxItemToRemove, cells)) &*& ListItem_t(pxItemToRemove, _, _, _, NULL);
{
    //@ open List_t(container, len, idx, end, cells);
    //@ assert DLS(end, ?endprev, end, endprev, cells, _);
    //@ split_DLS(end, endprev, end, endprev, pxItemToRemove, cells);
    //@ assert DLS(end, endprev, pxItemToRemove, ?itemprev, ?cells_of_DLS1, _);
    //@ assert DLS(pxItemToRemove, itemprev, end, endprev, ?cells_of_DLS2, _);
    //@ DLS_length_positive(pxItemToRemove, endprev);
    //@ join_cells(cells, cells_of_DLS1, cells_of_DLS2, pxItemToRemove);
    //@ length_append(cells_of_DLS1, cells_of_DLS2);

    /*@
    
    if (itemprev == end)
    {
        if (pxItemToRemove == endprev)
        {
    
            open DLS(pxItemToRemove, end, end, pxItemToRemove, cells_of_DLS2, _);
            open ListItem_t(pxItemToRemove, _, end, end, _);
            open DLS(end, pxItemToRemove, pxItemToRemove, end, cells_of_DLS1, _);
            open ListItem_t(end, _, pxItemToRemove, pxItemToRemove, _);
                
        } else
        {
        
            open DLS(pxItemToRemove, end, end, endprev, cells_of_DLS2, _);
            open ListItem_t(pxItemToRemove, _, ?itemnext, end, _);
            open DLS(itemnext, pxItemToRemove, end, endprev, tail(cells_of_DLS2), _);
            open ListItem_t(itemnext, _, _, pxItemToRemove, _); 
            open DLS(end, endprev, pxItemToRemove, end, cells_of_DLS1, _);
            open ListItem_t(end, _, pxItemToRemove, endprev, _);
        } 

    } else
    {
        if (pxItemToRemove == endprev)
        {
            open DLS(pxItemToRemove, itemprev, end, pxItemToRemove, cells_of_DLS2, _);
            open ListItem_t(pxItemToRemove, _, end, itemprev, _);
            length_append(cells_of_DLS1, cells_of_DLS2);
            DLS_extract_last_item(end, itemprev, cells_of_DLS1);
            open ListItem_t(itemprev, _, pxItemToRemove, ?itemprevprev, _);
            open DLS(end, pxItemToRemove, itemprev, itemprevprev, _, _);
            open ListItem_t(end, _, ?endnext, pxItemToRemove, _);

        } else 
        {
            open DLS(pxItemToRemove, itemprev, end, endprev, cells_of_DLS2, _);
            open ListItem_t(pxItemToRemove, _, ?itemnext, itemprev, _);
            DLS_extract_last_item(end, itemprev, cells_of_DLS1);
            open ListItem_t(itemprev, _, pxItemToRemove, ?itemprevprev, _);
            open DLS(itemnext, pxItemToRemove, end, endprev, tail(cells_of_DLS2), _);
            open ListItem_t(itemnext, _, _, pxItemToRemove, _);
        }
    }

    @*/ 
    
    
#ifdef VERIFAST /*< const pointer declaration */    
    List_t * pxList = pxItemToRemove->pxContainer;
#else
    List_t * const pxList = pxItemToRemove->pxContainer;
#endif

    pxItemToRemove->pxNext->pxPrevious = pxItemToRemove->pxPrevious;
    pxItemToRemove->pxPrevious->pxNext = pxItemToRemove->pxNext;

    mtCOVERAGE_TEST_DELAY();

    if( pxList->pxIndex == pxItemToRemove )
    {
        pxList->pxIndex = pxItemToRemove->pxPrevious;
    }
    else
    {
        mtCOVERAGE_TEST_MARKER();
    }

    pxItemToRemove->pxContainer = NULL;
    ( pxList->uxNumberOfItems )--;

    return pxList->uxNumberOfItems;
    
    /*@ 
    
    if (itemprev == end)
    {
        if (pxItemToRemove == endprev)
        {
            close ListItem_t(end, _, end, end, _);
            close DLS(end, end, end, end, cons(end, nil), _);
    
        } else
        {
            close ListItem_t(end, _, ?itemnext, endprev, _);
            close ListItem_t(itemnext, _, _, end, _);    
            close DLS(end, endprev, itemnext, end, cells_of_DLS1, _);
            close DLS(itemnext, end, end, endprev, tail(cells_of_DLS2), _);
            append_DLS(end, endprev, itemnext, end, end, endprev, cells_of_DLS1, tail(cells_of_DLS2));
        }

    } else
    {
    
        if (pxItemToRemove == endprev)
        {
            close ListItem_t(end, _, _, itemprev, _);
            close ListItem_t(itemprev, _, end, ?itemprevprev, container);

            if (itemprevprev == end) 
            {
                close DLS(end, itemprev, itemprev, end, cons(end, nil), _);

            } else
            {
                assert DLS(_, end, itemprev, itemprevprev, ?cells0, _);
                close DLS(end, itemprev, itemprev, itemprevprev, cons(end, cells0), _);
            }
   
        append_take_drop_n(cells_of_DLS1, length(cells_of_DLS1) - 1);      
        close DLS(itemprev, itemprevprev, end, itemprev, cons(itemprev, nil), container);
        append_DLS(end, itemprev, itemprev, itemprevprev, end, itemprev, take(length(cells_of_DLS1) - 1, cells_of_DLS1), cons(itemprev, nil));   
        mem_append(itemprev,take(length(cells_of_DLS1) - 1, cells_of_DLS1),cons(itemprev,nil));  
        remove_item(pxItemToRemove, cells);
        append_nil(cells_of_DLS1);

        } else
        {
        
            close ListItem_t(itemprev, _, ?itemnext, ?itemprevprev, container);
            close ListItem_t(itemnext, _, _, itemprev, _);
            close DLS(itemnext, itemprev, end, endprev, tail(cells_of_DLS2), container);
            close DLS(itemprev, itemprevprev, itemnext, itemprev, cons(itemprev, nil), container);
            append_DLS(end, endprev, itemprev, itemprevprev, itemnext, itemprev, take(length(cells_of_DLS1) - 1, cells_of_DLS1), cons(itemprev, nil));
            append_take_drop_n(cells_of_DLS1, length(cells_of_DLS1) - 1);
            mem_append(itemprev,take(length(cells_of_DLS1) - 1, cells_of_DLS1),cons(itemprev, nil));
            mem_append(itemprev,cells_of_DLS1, tail(cells_of_DLS2));
            append_DLS(end, endprev, itemnext, itemprev, end, endprev, cells_of_DLS1, tail(cells_of_DLS2));
            remove_item(pxItemToRemove, cells);
            open DLS(end, endprev, end, endprev, remove(pxItemToRemove, cells), _);
            close DLS(end, endprev, end, endprev, remove(pxItemToRemove, cells), _);
        }
    }
    
    @*/
    
    //@ length_remove(pxItemToRemove, cells);
    
    /*@ 

    if (idx == pxItemToRemove)
    {
        close List_t(container, len-1, itemprev, end, remove(pxItemToRemove, cells));
        
    } else
    {
        remove_member(idx, pxItemToRemove, cells);
        close List_t(container, len-1, idx, end, remove(pxItemToRemove, cells));
    }
    
    @*/

    //@ close ListItem_t(pxItemToRemove, _, _, _, NULL);
}