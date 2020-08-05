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

#ifdef VERIFAST /* choose function */
ListItem_t * choose(List_t * list);
    //@ requires DLS(&(list->xListEnd), ?endprev, &(list->xListEnd), endprev, ?cells, ?container);
    //@ ensures DLS(&(list->xListEnd), endprev, &(list->xListEnd), endprev, cells, container) &*& mem(result, cells) == true;
#endif

void vListInsert( List_t * const pxList,
                  ListItem_t * const pxNewListItem )
    //@ requires List_t(pxList, ?len, ?idx, ?end, ?cells) &*& ListItem_t(pxNewListItem, ?val, _, _, _);
    //@ ensures List_t(pxList, len+1, idx, end, ?newcells) &*& (remove(pxNewListItem, newcells) == cells);
{
    ListItem_t * pxIterator;

    //@ open List_t(pxList, len, idx, end, cells);
    //@ assert DLS(end, ?endprev, end, endprev, cells, _);
    //@ index_of_last_in_DLS(end, endprev, cells);
    //@ DLS_star_item(end, endprev, pxNewListItem);
    //@ open ListItem_t(pxNewListItem, _, _, _, _);
    
    const TickType_t xValueOfInsertion = pxNewListItem->xItemValue;

    /* Only effective when configASSERT() is also defined, these tests may catch
     * the list data structures being overwritten in memory.  They will not catch
     * data errors caused by incorrect configuration or use of FreeRTOS. */
    listTEST_LIST_INTEGRITY( pxList );
    listTEST_LIST_ITEM_INTEGRITY( pxNewListItem );


    /* Insert the new list item into the list, sorted in xItemValue order.
     *
     * If the list already contains a list item with the same item value then the
     * new list item should be placed after it.  This ensures that TCBs which are
     * stored in ready lists (all of which have the same xItemValue value) get a
     * share of the CPU.  However, if the xItemValue is the same as the back marker
     * the iteration loop below will not end.  Therefore the value is checked
     * first, and the algorithm slightly modified if necessary. */
    if( xValueOfInsertion == portMAX_DELAY )
    {
        //@ open DLS(end, endprev, end, endprev, cells, _);
    
        /*@
       
        if (end == endprev)
        {
            open ListItem_t(end, _, end, end, _);
            
        } 
        else
        {
            open ListItem_t(end, _, ?endnext, endprev, _);
            DLS_length_positive(endnext, endprev);
            
            if (endnext == endprev)
            {
                open DLS(endprev, _, _, endprev, _, _);
                
            } 
            else 
            {
                DLS_extract_last_item(endnext, endprev, tail(cells));
            }
        
        open ListItem_t(endprev, _, end, _, _);
            
        }
        @*/
    
        pxIterator = pxList->xListEnd.pxPrevious;
    }
    else
    {
        /* *** NOTE ***********************************************************
        *  If you find your application is crashing here then likely causes are
        *  listed below.  In addition see https://www.freertos.org/FAQHelp.html for
        *  more tips, and ensure configASSERT() is defined!
        *  https://www.freertos.org/a00110.html#configASSERT
        *
        *   1) Stack overflow -
        *      see https://www.freertos.org/Stacks-and-stack-overflow-checking.html
        *   2) Incorrect interrupt priority assignment, especially on Cortex-M
        *      parts where numerically high priority values denote low actual
        *      interrupt priorities, which can seem counter intuitive.  See
        *      https://www.freertos.org/RTOS-Cortex-M3-M4.html and the definition
        *      of configMAX_SYSCALL_INTERRUPT_PRIORITY on
        *      https://www.freertos.org/a00110.html
        *   3) Calling an API function from within a critical section or when
        *      the scheduler is suspended, or calling an API function that does
        *      not end in "FromISR" from an interrupt.
        *   4) Using a queue or semaphore before it has been initialised or
        *      before the scheduler has been started (are interrupts firing
        *      before vTaskStartScheduler() has been called?).
        **********************************************************************/
        
#ifdef VERIFAST /* overapproximate loop */    
        pxIterator = choose(pxList);
#else
        for( pxIterator = ( ListItem_t * ) &( pxList->xListEnd ); pxIterator->pxNext->xItemValue <= xValueOfInsertion; pxIterator = pxIterator->pxNext ) /*lint !e826 !e740 !e9087 The mini list structure is used as the list end to save RAM.  This is checked and valid. *//*lint !e440 The iterator moves to a different value, not xValueOfInsertion. */
        {
            /* There is nothing to do here, just iterating to the wanted
             * insertion position. */
        }
#endif
        
        /*@
        
        if(pxIterator == end)
        {
            open DLS(end, endprev, end, endprev, cells, _);
            open ListItem_t(end, _, ?endnext, endprev, _);
            
            if (end != endprev)
            {
                open DLS(endnext, end, end, endprev, tail(cells), _);
                open ListItem_t(endnext, _, _, end, _); 
            }

        } 
        else
        {

            split_DLS(end, endprev, end, endprev, pxIterator, cells);
            assert DLS(end, endprev, pxIterator, ?iterprev, ?cells1, _);
            assert DLS(pxIterator, iterprev, end, endprev, ?cells2, _);
            open DLS(pxIterator, iterprev, end, endprev, cells2, _);
            open ListItem_t(pxIterator, _, ?iternext, iterprev, _);
            
            if (pxIterator == endprev)
            {
                open DLS(end, endprev, pxIterator, iterprev, cells1, _);
                open ListItem_t(iternext, _, _, pxIterator, _); 
                
            } 
            else
            {
                open DLS(iternext, pxIterator, end, endprev, tail(cells2), _);
                open ListItem_t(iternext, _, _, pxIterator, _);
            }
        }
        @*/

    }

    pxNewListItem->pxNext = pxIterator->pxNext;
    pxNewListItem->pxNext->pxPrevious = pxNewListItem;
    pxNewListItem->pxPrevious = pxIterator;
    pxIterator->pxNext = pxNewListItem;

    /* Remember which list the item is in.  This allows fast removal of the
     * item later. */
    pxNewListItem->pxContainer = pxList;

    ( pxList->uxNumberOfItems )++;
    
    //@ close ListItem_t(pxNewListItem, _, ?iternext, pxIterator, _);
    //@ close ListItem_t(pxIterator, _, pxNewListItem, ?iterprev, _);
    
    /*@
    
    if (xValueOfInsertion == portMAX_DELAY)
    {
    
        if (end == endprev)
        {
           close DLS(pxNewListItem, end, end, pxNewListItem, cons(pxNewListItem, nil), _);
           close DLS(end, pxNewListItem, end, pxNewListItem, cons(end, cons(pxNewListItem,nil)), _);
           close List_t(pxList, len+1, idx, end, cons(end, cons(pxNewListItem, nil)));
           
        } 
        else
        {
         
           close ListItem_t(end, _, ?endnext, pxNewListItem, _);
           close DLS(pxNewListItem, endprev, end, pxNewListItem, cons(pxNewListItem, nil), _);
           close DLS(endprev, iterprev, end, pxNewListItem, cons(endprev, cons(pxNewListItem, nil)), _);
           
           if (endnext == endprev)
           {
               close DLS(iterprev, pxNewListItem, end, pxNewListItem, cons(iterprev, cons(endprev, cons(pxNewListItem, nil))), _);
               close List_t(pxList, len+1, idx, end, cons(iterprev, cons(endprev, cons(pxNewListItem, nil))));

           } 
           else
           {
               assert DLS(endnext, end, endprev, iterprev, ?cells0, _);
               append_DLS(endnext, end, endprev, iterprev, end, pxNewListItem, cells0, cons(endprev, cons(pxNewListItem, nil)));
               close DLS(end, pxNewListItem, end, pxNewListItem, cons(end, append(cells0, cons(endprev, cons(pxNewListItem, nil)))), _);
               append_take_drop_n(cells, length(cells) - 1);
               append_assoc(cons(end, cells0), cons(endprev, nil), cons(pxNewListItem, nil));
               remove_append(pxNewListItem, cells, cons(pxNewListItem, nil));
               close List_t(pxList, len+1, idx, end, append(cells, cons(pxNewListItem, nil)));  
           }
        }
    
    } 
    else
    {
    
        if (pxIterator == end)
        {
        
            if (iternext == end)
            {
                close DLS(pxNewListItem, pxIterator, end, pxNewListItem, cons(pxNewListItem,nil), _);
                close DLS(end, pxNewListItem, end, pxNewListItem, cons(end,cons(pxNewListItem,nil)), _);
                close List_t(pxList, len+1, idx, end, cons(end, cons(pxNewListItem, nil)));
        
            } 
            else
            {
                close ListItem_t(iternext, _, _, pxNewListItem, _);
            
                if (iternext == endprev)
                {
                    close DLS(iternext, pxNewListItem, end, endprev, cons(iternext, nil), _);
                    last_element_in_DLS(iternext, endprev, cons(iternext, nil));
                
                } 
                else
                {
                    assert DLS(_, iternext, end, endprev, ?cells2, _);
                    close DLS(iternext, pxNewListItem, end, endprev, cons(iternext,cells2), _);
                    last_element_in_DLS(iternext, endprev, cons(iternext, cells2));
                
                }
            
                assert DLS(iternext, pxNewListItem, end, endprev, ?cells2, _);
                DLS_star_item(iternext, endprev, pxNewListItem);
                
                close DLS(pxNewListItem, pxIterator, end, endprev, cons(pxNewListItem, cells2), _);
                close DLS(end, endprev, end, endprev, cons(end, cons(pxNewListItem, cells2)), _);
                close List_t(pxList, len+1, idx, end, cons(end, cons(pxNewListItem, cells2)));
            
            }
           
        
        } 
        else
        {
        
            if (pxIterator == endprev)
            {
                close ListItem_t(iternext, _, ?o, pxNewListItem, _);
            
                if (iterprev == end)
                {
                    close DLS(end, pxNewListItem, pxIterator, end, cons(end, nil), _);
                
                } 
                else
                {
                    assert DLS(_, iternext, pxIterator, iterprev, ?cells1, _);
                    close DLS(end, pxNewListItem, pxIterator, iterprev, cons(end, cells1), _);
                }
            
                assert DLS(end, pxNewListItem, pxIterator, iterprev, ?cells1, _);
                close DLS(pxNewListItem, pxIterator, iternext, pxNewListItem, cons(pxNewListItem, nil), _);
                close DLS(pxIterator, iterprev, iternext, pxNewListItem, cons(pxIterator, cons(pxNewListItem, nil)), _);
                append_DLS(end, pxNewListItem, pxIterator, iterprev, iternext, pxNewListItem, cells1, cons(pxIterator,cons(pxNewListItem,nil)));
                drop_n_plus_one(index_of(pxIterator, cells), cells);
                index_of_nth(pxIterator, cells);
                append_take_drop_n(cells, index_of(pxIterator, cells));
                remove_append(pxNewListItem, cells1, cons(pxIterator, cons(pxNewListItem, nil)));
                close List_t(pxList, len+1, idx, end, append(cells1, cons(pxIterator,cons(pxNewListItem,nil))));  
         
            } 
            else
            {
                close ListItem_t(iternext, _, _, pxNewListItem, _);
            
                if (iternext == endprev)
                {
                    close DLS(iternext, pxNewListItem, end, endprev, cons(iternext, nil), _);
                
                } 
                else
                {
                    assert DLS(_, iternext, end, endprev, ?cells2, _);
                    close DLS(iternext, pxNewListItem, end, endprev, cons(iternext, cells2), _);
                } 
            
                assert DLS(end, endprev, pxIterator, iterprev, ?cells1, _);
                DLS_length_positive(end, iterprev);
                head_take(pxIterator, cells);
                assert DLS(iternext, pxNewListItem, end, endprev, ?cells2, _);
                last_element_in_DLS(iternext, endprev, cells2);
                DLS_star_item(iternext, endprev, pxNewListItem);
                close DLS(pxNewListItem, pxIterator, end, endprev, cons(pxNewListItem, cells2), _);
                close DLS(pxIterator, iterprev, end, endprev, cons(pxIterator, cons(pxNewListItem, cells2)), _);  
                append_DLS(end, endprev, pxIterator, iterprev, end, endprev, cells1, cons(pxIterator, cons(pxNewListItem, cells2)));
                head_append(cells1, cons(pxIterator, cons(pxNewListItem, cells2)));   
                drop_n_plus_one(index_of(pxIterator, cells), cells);
                index_of_nth(pxIterator, cells);
                append_take_drop_n(cells, index_of(pxIterator, cells));
                remove_append(pxNewListItem, cells1, cons(pxIterator, cons(pxNewListItem, cells2)));
                close List_t(pxList, len+1, idx, end, append(cells1, cons(pxIterator, cons(pxNewListItem, cells2))));   
            }
        }       
    }
    
    @*/
}