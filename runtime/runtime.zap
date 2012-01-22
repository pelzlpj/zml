.NEW 5   ; Specify output format as Z-machine version 5

; Place Z-machine header in first 64 bytes
.INSERT "header.zap"

; Place array of globals in bytes [64, 64 + 240*2 == 544)
.INSERT "globals.zap"

; Last word in the lower 64K is reserved for the 'main' routine (initial
; PC must be represented in two bytes for storage in the header). So, 
; subtracting off the size of the globals and header, 65534-544=64990
; gives us the RAM remaining for heap usage.  Here is the value in words:
HEAP_WORDS=32495

; We set the high bit to indicate a memory block which is a freelist cons cell
FREELIST_BIT=32768
FREELIST_SIZE_MASK=32767

; Zero is a valid freelist location, so we have to choose something different
; for NULL
LIST_NULL=65535


MARK_BIT=16384          ; Second-highest bit is the mark bit
NOT_MARK_BIT=49151
TAG_MASK=15360          ; Four bits for the tag
HEADER_DATA_MASK=1023   ; Bottom ten bits hold type-specific data


; The following are pre-shifted by 10 bits for ease of comparison
VALUEARRAY_TAG=0     ; Header bits for a value array cell
REFARRAY_TAG=1024    ; Header bits for a reference array cell
VALUELIST_TAG=2048   ; Header bits for a value list cell
REFLIST_TAG=3072     ; Header bits for a reference list cell



; Insert zeros for the empty space until end of dynamic area
__heap_start::
.INSERT "empty_heap.zap"

__begin_static::
__begin_high::

__zml_main::
   call_1n __zml_init_heap
   call_1n zml_main  ; jumping to user code entry point
   quit


.FUNCT __main, ref1, ref2, ref3, root1, root2, root3
   call_vs zml_alloc_value_array 5 15  -> ref1
   call_vs zml_alloc_value_array 4 10  -> ref2
   call_2s zml_register_root ref2 -> root2
   call_vs zml_alloc_value_array 1 8  -> ref1
   call_2s zml_register_root ref1 -> root1

   print "registered root: "
   print_num root1
   new_line

   loadw __heap_start root1 -> sp
   print "heap_ptr: "
   print_num sp
   new_line

   call_1n __zml_mark_roots
   call_1n __zml_sweep
   call_1n __zml_compact

   loadw __heap_start root1 -> ref1
   print "heap pointer was relocated to "
   print_num ref1
   new_line

   call_vs zml_array_get ref1 0 -> sp
   print "heap array holds value "
   print_num sp
   new_line

   save -> sp

   call_2n zml_unregister_root root2
   call_1n __zml_mark_roots
   call_1n __zml_sweep
   call_1n __zml_compact

   loadw __heap_start root1 -> ref1
   print "heap pointer was relocated to "
   print_num ref1
   new_line

   call_vs zml_array_get ref1 0 -> sp
   print "heap array holds value "
   print_num sp
   new_line

   save -> sp
   rtrue
   

.FUNCT __zml_init_heap
   ; Initialize the heap with zero words allocated.  We end up with
   ; a freelist with one entry representing almost the entire heap;
   ; one word is reserved for a root table freelist of size 1.
   sub HEAP_WORDS 1 -> sp
   call_vn __zml_freelist_node_cons 0 sp LIST_NULL
   store 'freelist_head 0
   store 'freelist_end  0

   sub HEAP_WORDS 1 -> root_freelist_head
   storew __heap_start root_freelist_head LIST_NULL
   rtrue


.FUNCT zml_alloc_value_array, size, init_val
   ; Allocate a new array of the given size, which shall hold values (not pointers).
   ; The initial value is assigned to all elements.
   ;
   ; param size: length of the array >= 0, in words
   ; param init_val: initial value to store in all locations
   ;
   ; Returns: word index where array begins (heap-relative)
   call_vs __zml_alloc_array size init_val VALUEARRAY_TAG -> sp
   ret_popped


.FUNCT zml_alloc_ref_array, size, init_val
   ; Allocate a new array of the given size, which shall hold pointers (not values).
   ; The initial pointer value is assigned to all elements.
   ;
   ; param size: length of the array >= 0, in words
   ; param init_val: initial value to store in all locations
   ;
   ; Returns: word index where array begins (heap-relative)
   call_vs __zml_alloc_array size init_val REFARRAY_TAG -> sp
   ret_popped


NOT_ONE=65534           ; bitwise not of 1

.FUNCT __zml_alloc_array, size, init_val, header_word, curr_word
   ; Allocate a new array of the given size, applying the specified array header
   ; to the reference cell. The initial value is assigned to all elements.
   ;
   ; param size: length of the array >= 0, in words
   ; param init_val: initial value to store in all locations
   ; param header_word: word to be placed in the array header
   ; local curr_word: current word being written
   ;
   ; Returns: word index where array begins (heap-relative)
   jl size HEADER_DATA_MASK ?small_array           ; jump if size is small enough for compact representation

large_array:
   add size 3 -> sp
   and sp NOT_ONE -> sp                            ; even size ==> sp = size+2; odd size ==> sp = size+3
   call_2s __zml_alloc_block sp -> curr_word
   push curr_word                                  ; leave a copy of array reference on the stack
   or header_word HEADER_DATA_MASK -> header_word  ; header now identifies this as large array
   storew __heap_start curr_word header_word
   inc 'curr_word
   storew __heap_start curr_word size
   jump fill_words

small_array:
   add size 2 -> sp
   and sp NOT_ONE -> sp                            ; even size ==> sp = size+2; odd size ==> sp = size+1
   call_2s __zml_alloc_block sp -> curr_word
   push curr_word                                  ; leave a copy of array reference on the stack
   or header_word size -> header_word
   storew __heap_start curr_word header_word

fill_words:
   jz size ?done                                   ; jump if size is zero
   inc 'curr_word
   storew __heap_start curr_word init_val
   dec 'size
   jump fill_words

done:
   ret_popped


.FUNCT zml_array_size, arr, header_size
   ; Retrieve the size of the specified array.
   ;
   ; param arr: word index where array begins (heap-relative)
   ; local header_size: size of array recorded in the array header
   ;
   ; Returns: array size
   loadw __heap_start arr -> sp
   and sp HEADER_DATA_MASK -> header_size
   jl header_size HEADER_DATA_MASK ?small_array   ; jump if this is array uses compact representation
   inc 'arr
   loadw __heap_start arr -> sp
   ret_popped

small_array:
   ret header_size


.FUNCT __zml_array_get_element_address, arr, index
   ; Retrieve the physical address of the given array location.
   ;
   ; param arr: word index where array begins (heap-relative)
   ; param index: array location to retrieve; 0 <= index < array size
   ;
   ; Returns: word index where element is stored, relative to heap start
   loadw __heap_start arr -> sp
   and sp HEADER_DATA_MASK -> sp
   jl sp HEADER_DATA_MASK ?small_array             ; jump if this array uses compact representation
   add arr 2 -> sp
   add sp index -> sp
   ret_popped

small_array:
   add arr 1 -> sp
   add sp index -> sp
   ret_popped


.FUNCT zml_array_get, arr, index
   ; Retrieve the value stored in the array at the given index.
   ;
   ; param arr: word index where array begins (heap-relative)
   ; param index: array value to retrieve; 0 <= index < array size
   ;
   ; Returns: array value
   call_vs __zml_array_get_element_address arr index -> sp
   loadw __heap_start sp -> sp
   ret_popped
   

.FUNCT zml_array_set, arr, index, val
   ; Set the value stored in the array at the given index.
   ;
   ; param arr: word index where array begins (heap-relative)
   ; param index: array value to set; 0 <= word < array size
   ; param val: word to place in array
   call_vs __zml_array_get_element_address arr index -> sp
   storew __heap_start sp val
   rtrue


.FUNCT __zml_array_mark_children, ref, is_set, count
   ; Recursively set or clear the 'mark' bit on all children belonging to
   ; this array.
   ;
   ; param ref: word index where array cell begins (heap-relative)
   ; param is_set: 1 if mark should be set, 0 if cleared
   ; local count: loop counter
   call_2s zml_array_size ref -> count

   ; marking children in reverse order as we count down to 0
mark_children:
   jz count ?done                            ; jump if count reaches zero
   dec 'count
   call_vs zml_array_get ref count -> sp
   call_vn __zml_mark_recursive sp is_set    ; mark child
   jump mark_children

done:
   rtrue


.FUNCT __zml_array_iter_inplace, ref, f, arg2, arg3, i, size
   ; Applies 'f' to the physical address of each array element, in turn.
   ;
   ; param ref: word index where array cell begins (heap-relative)
   ; param f: function of four arguments, applied in turn to the heap-relative
   ;     word address of each element.
   ; param arg2, arg3: generic arguments passed to f
   ; local i: counter
   ; local size: size of array
   store 'i 0
   call_2s zml_array_size ref -> size

loop:
   jeq i size ?done                          ; jump if array has been traversed
   call_vs __zml_array_get_element_address ref i -> sp
   call_vn f sp arg2 arg3
   inc 'i
   jump loop

done:
   rtrue


.FUNCT __zml_array_storage_size, ref
   ; Gets the storage size reserved for this array, in words.
   ;
   ; param ref: word index where array begins (heap-relative)
   ;
   ; Returns: storage size
   loadw __heap_start ref -> sp
   and sp HEADER_DATA_MASK -> sp
   jl sp HEADER_DATA_MASK ?small_array             ; jump if this array uses compact representation
   call_2s zml_array_size ref -> sp
   add sp 3 -> sp
   and sp NOT_ONE -> sp   ; even size ==> sp = size+2; odd size ==> sp = size+3
   ret_popped

small_array:
   call_2s zml_array_size ref -> sp
   add sp 2 -> sp
   and sp NOT_ONE -> sp   ; even size ==> sp = size+2; odd size ==> sp = size+1
   ret_popped


.FUNCT zml_alloc_value_list, init_val, next_cell
   ; Allocate a list cell, which shall contain the given initial
   ; reference value and pointer to the next cell.  The cell contents shall
   ; be treated as a pointer (not a value).
   ;
   ; param init_val: initial value to store in cell
   ; param next_cell: pointer to next list cell, or LIST_NULL
   ;
   ; Returns: word index where cell begins (heap-relative)
   call_vs __zml_alloc_list init_val next_cell VALUELIST_TAG -> sp
   ret_popped


.FUNCT zml_alloc_ref_list, init_val, next_cell
   ; Allocate a list cell, which shall contain the given initial value
   ; and pointer to the next cell.  The cell contents shall be treated
   ; as a value (not a pointer).
   ;
   ; param init_val: initial value to store in cell
   ; param next_cell: pointer to next list cell, or LIST_NULL
   ;
   ; Returns: word index where cell begins (heap-relative)
   call_vs __zml_alloc_list init_val next_cell REFLIST_TAG -> sp
   ret_popped


.FUNCT __zml_alloc_list, init_val, next_cell, header_word, ref
   ; Allocate a list cell, which shall contain the given initial value
   ; and pointer to the next cell.  The list shall be created with the
   ; specified header word.
   ;
   ; param init_val: initial value to place in cell
   ; param next_cell: pointer to next cell, or LIST_NULL
   ; param header_word: header value to place in cell
   ; local ref: holds a reference to the allocated block
   ;
   ; Returns: word index where cell begins (heap-relative)
   call_2s __zml_alloc_block 4 -> ref
   storew __heap_start ref header_word
   add ref 1 -> sp
   storew __heap_start sp init_val
   add ref 2 -> sp
   storew __heap_start sp next_cell
   ret ref


.FUNCT zml_list_head, list
   ; Retrieve the value stored in the given list cell.
   ;
   ; param list: word index where list cell begins (heap-relative)
   ;
   ; Returns: value
   inc 'list
   loadw __heap_start list -> sp
   ret_popped


.FUNCT zml_list_tail, list
   ; Retrieve the location of the list cell which is pointed to
   ; by the given cell.
   ;
   ; param list: word index where list cell begins (heap-relative)
   ;
   ; Returns: next list cell, or LIST_NULL if end-of-list
   add list 2 -> sp
   loadw __heap_start sp -> sp
   ret_popped


.FUNCT __zml_value_list_mark_children, ref, is_set
   ; Recursively set or clear the 'mark' bit on the chain of list cells to
   ; which this cell links.  The value contained in this list cell is
   ; *not* marked.
   ;
   ; param ref: word index where list cell begins (heap-relative)
   ; param is_set: 1 if mark should be set, 0 if cleared
   call_2s zml_list_tail ref -> ref
   jeq ref LIST_NULL ?end_of_list
   call_vn __zml_mark_recursive ref is_set
end_of_list:
   rtrue


.FUNCT __zml_value_list_fixup_pointers, ref, table, table_dwords, pointer_addr
   ; Given a break table, adjusts the value of the pointer stored
   ; in this value list cell (if any).
   ;
   ; param ref: word index where list cell begins (heap-relative)
   ; param table: word index where break table begins (heap-relative)
   ; param table_dwords: length of break table, in dwords
   ; local pointer_addr: location of value to be fixed up
   add ref 2 -> pointer_addr
   loadw __heap_start pointer_addr -> sp
   jeq sp LIST_NULL ?end_of_list
   call_vn __zml_fixup_pointer pointer_addr table table_dwords
end_of_list:
   rtrue


.FUNCT __zml_ref_list_fixup_pointers, ref, table, table_dwords, pointer_addr
   ; Given a break table, adjusts the value of the pointers stored
   ; in this reference list cell.
   ;
   ; param ref: word index where list cell begins (heap-relative)
   ; param table: word index where break table begins (heap-relative)
   ; param table_dwords: length of break table, in dwords
   ; local pointer_addr: location of value to be fixed up
   add ref 1 -> pointer_addr
   loadw __heap_start pointer_addr -> sp
   call_vn __zml_fixup_pointer pointer_addr table table_dwords          ; fixup head
   call_vn __zml_value_list_fixup_pointers ref table table_dwords       ; fixup tail
   rtrue


.FUNCT __zml_ref_list_mark_children, ref, is_set
   ; Recursively set or clear the 'mark' bit on all children belonging to
   ; this list cell, and on the chain of list cells to which this cell
   ; links.
   ;
   ; param ref: word index where list cell begins (heap-relative)
   ; param is_set: 1 if mark should be set, 0 if cleared
   call_2s zml_list_head ref -> sp
   call_vn __zml_mark_recursive sp is_set
   call_vn __zml_value_list_mark_children ref is_set
   rtrue


.FUNCT __zml_mark_recursive, ref, is_set, tag
   ; Check whether the 'mark' bit on this block is set or clear.  If it
   ; differs from the requested setting, then toggle the state and recursively
   ; apply the setting to all child blocks.
   ;
   ; param ref: word index where block begins (heap-relative)
   ; param is_set: 1 if mark should be set, 0 if cleared
   ; local tag: stores value of block tag
   call_vs __zml_mark ref is_set -> sp
   jz sp ?already_marked                  ; jump if already marked
   call_2s __zml_tag_get ref -> tag       ; dispatch based on tag value
   jeq tag REFARRAY_TAG  ?ref_array
   jeq tag VALUELIST_TAG ?value_list
   jeq tag REFLIST_TAG   ?ref_list
   rtrue                                  ; default case: no pointers to children

already_marked:
   rtrue

ref_array:
   call_vn __zml_array_mark_children ref is_set
   rtrue

value_list:
   call_vn __zml_value_list_mark_children ref is_set
   rtrue

ref_list:
   call_vn __zml_ref_list_mark_children ref is_set
   rtrue


.FUNCT __zml_mark, ref, is_set, header
   ; Set or clear the 'mark' bit on this block.
   ;
   ; param ref: word index where block begins (heap-relative)
   ; param is_set: 1 if mark should be set, 0 if cleared
   ; local header: old value of header
   ;
   ; Returns: true if the bit needed to be changed, false otherwise
   loadw __heap_start ref -> header 
   and header MARK_BIT -> sp
   jz is_set ?clear                       ; jump if clear is requested

   jz sp ?~no_change                      ; jump if mark bit was already set
   or header MARK_BIT -> sp               ; otherwise set it
   storew __heap_start ref sp
   rtrue

clear:
   jz sp ?no_change                       ; jump if mark bit was already clear
   and header NOT_MARK_BIT -> sp          ; otherwise clear it
   storew __heap_start ref sp
   rtrue

no_change:
   rfalse


.FUNCT __zml_allocated_block_size, ref, tag
   ; Determines the number of words in an allocated memory block.
   ;
   ; param ref: word index where block begins (heap-relative)
   ; local tag: storage for the block tag
   call_2s __zml_tag_get ref -> tag       ; dispatch based on tag value
   jeq tag VALUEARRAY_TAG ?tag_array
   jeq tag REFARRAY_TAG   ?tag_array
   jeq tag VALUELIST_TAG  ?tag_list
   jeq tag REFLIST_TAG    ?tag_list

tag_array:
   call_2s __zml_array_storage_size ref -> sp
   ret_popped

tag_list:
   push 4
   ret_popped


.FUNCT __zml_sweep, block, freelist_last, header, size
   ; Sweeps the marked heap.  Unmarked blocks are assigned to a newly-created
   ; freelist.  Marked blocks become unmarked.
   ;
   ; Note that the freelist is created in strictly increasing address order.
   ;
   ; local block: word index of current block
   ; local freelist_last: most recently created freelist node, at the end of the
   ;     list
   ; local header: storage for a header word
   ; local size: size of current block
   store 'freelist_head LIST_NULL
   store 'block 0
   store 'freelist_last LIST_NULL

traverse_next:
   jeq block freelist_end ?end_traversal                             ; jump if entire heap was examined
   loadw __heap_start block -> header
   and header FREELIST_BIT -> sp
   jz sp ?block_was_allocated                                        ; jump if this block was allocated memory

block_was_free:
   call_2s __zml_freelist_node_size block -> size

block_is_free:
   jeq freelist_last LIST_NULL ?block_is_first_free                  ; jump if this is the first free block
   call_2s __zml_freelist_node_next freelist_last -> sp              ; sp contains block following last freelist entry
   jeq sp block ?coalesce_free_blocks                                ; jump if this free block is adjacent to previous
   call_2s __zml_freelist_node_size freelist_last -> sp              ; sp contains size of last freelist entry
   call_vn __zml_freelist_node_cons freelist_last sp block           ; make freelist_last point to current block
   add block size -> sp                                              ; sp contains location immediately following current block
   call_vn __zml_freelist_node_cons block size sp                    ; current block now points to block immediately following
   store 'freelist_last block                                        ; current block is now last in the freelist
   add block size -> block
   jump traverse_next                                                ; process block immediately after current
   
coalesce_free_blocks:
   add block size -> sp                                              ; sp contains location immediately following current block
   call_2s __zml_freelist_node_size freelist_last -> sp
   add size sp -> sp                                                 ; sp contains size of coalesced block
   call_vn __zml_freelist_node_cons freelist_last sp sp              ; freelist_last is extended in-place
   add block size -> block
   jump traverse_next                                                ; process block immediately after current

block_is_first_free:
   store 'freelist_head block
   store 'freelist_last block
   add block size -> sp                                              ; sp points to next block
   call_vn __zml_freelist_node_cons block size sp
   add block size -> block
   jump traverse_next                                                ; process block immediately after current

block_was_allocated:
   call_2s __zml_allocated_block_size block -> size
   call_vs __zml_mark block 0 -> sp                                  ; unmark block; sp == 1 iff block was marked
   jz sp ?block_is_free                                              ; jump if this allocated block is unreachable

reachable_allocated_block:
   ; nothing to do
   add block size -> block
   jump traverse_next                                                ; process block immediately after current

end_traversal:
   jeq freelist_last LIST_NULL ?no_new_freelist                      ; jump if no freelist entries created
   call_2s __zml_freelist_node_size freelist_last -> sp
   call_vn __zml_freelist_node_cons freelist_last sp freelist_end    ; append freelist_end to the freelist
   rtrue

no_new_freelist:
   store 'freelist_head freelist_end
   rtrue


.FUNCT __zml_compact, table_dwords, source, dest, size, freelist_next
   ; Compacts the heap, using a Haddon-Waite-style algorithm.  This is
   ; typically called when the heap has been freshly swept.
   ;
   ; The implementation uses an optimization which is not present in
   ; Haddon-Waite: the break table is constructed on the stack in
   ; a single pass, then relocated to free heap memory after the
   ; memory contents are moved.  This approach avoids the need to
   ; "roll the table" and sort it.
   ;
   ; local table_dwords: number of break table entries
   ; local source: address of a block to be moved
   ; local dest: address where block should be moved
   ; local size: size of the block to move
   ; local freelist_next: next node in the freelist
   store 'table_dwords 0
   jeq freelist_head freelist_end ?end_traversal                     ; jump if all free memory is at the end

traverse_freelist:
   ; figure out the size of a block to move, and how far to move it
   load 'freelist_head -> dest                                       ; word address where block gets moved
   call_2s __zml_freelist_node_size freelist_head -> sp
   add freelist_head sp -> source                                    ; word address where block starts
   call_2s __zml_freelist_node_next freelist_head -> freelist_next
   sub freelist_next freelist_head -> size
   call_2s __zml_freelist_node_size freelist_head -> sp
   sub size sp -> size                                               ; number of words in the block
   add freelist_head size -> freelist_head                           ; new location for free space

   ; construct break table entry for this relocation; because we copy from the stack
   ; to heap going from high addresses to low, the table values on the heap will be
   ; ordered as (pointer, distance), (pointer, distance), ...
   push source                      ; push pointer
   sub source dest -> sp            ; push relocation distance
   inc 'table_dwords

   ; translate these heap-relative word addresses into byte addresses
   ; FIXME: do I have to worry about signed arithmetic here?
   log_shift source 1 -> source
   add source __heap_start -> source
   log_shift dest 1 -> dest
   add dest __heap_start -> dest
   mul size 2 -> size

   ; relocate the block
   copy_table source dest size

   ; construct a new freelist entry for the merged free space
   call_2s __zml_freelist_node_size freelist_next -> size
   add freelist_next size -> size
   sub size freelist_head -> size                                    ; new size of merged freelist node
   call_2s __zml_freelist_node_next freelist_next -> freelist_next   ; next_ptr for merged freelist node
   call_vn __zml_freelist_node_cons freelist_head size freelist_next 
   jeq freelist_next LIST_NULL ?end_traversal                        ; jump if merged node is end-of-list
   jump traverse_freelist

end_traversal:
   load 'freelist_head -> freelist_end
   ; move the break table to the heap (copy is done in reverse to keep the table ordered)
   call_2s __zml_freelist_node_size freelist_end -> sp
   add freelist_end sp -> dest                                       ; dest is at the very end of heap memory (+ 1)
   mul table_dwords 2 -> size

copy_break_table:
   jz size ?copy_done
   dec 'dest
   storew __heap_start dest sp
   dec 'size
   jump copy_break_table

copy_done:
   call_vn __zml_compact_fixup_pointers dest table_dwords
   rtrue


.FUNCT __zml_compact_fixup_pointers, table, table_dwords, block, tag, roots_table_boundary
   ; Modify all the pointers stored on the heap, using the transformations specified
   ; in the break table.
   ;
   ; param table: word address where break table begins (heap-relative)
   ; param table_dwords: length of break table, in double-words
   ; local block: pointer to current block (heap-relative)
   ; local tag: storage for block tag
   ; local roots_table_boundary: any pointers >= this address are root freelist
   ;     entries; otherwise they are heap pointers to be marked
   store 'block 0

traverse_compacted:
   jeq block freelist_head ?end_traversal                            ; jump if we reach end of compacted heap
   call_2s __zml_tag_get block -> tag                                ; dispatch based on tag value
   jeq tag VALUEARRAY_TAG ?fixup_done
   jeq tag REFARRAY_TAG   ?tag_ref_array
   jeq tag VALUELIST_TAG  ?tag_value_list
   jeq tag REFLIST_TAG    ?tag_ref_list

tag_ref_array:
   call_vn2 __zml_array_iter_inplace block __zml_fixup_pointer table table_dwords
   jump fixup_done

tag_value_list:
   call_vn __zml_value_list_fixup_pointers block table table_dwords
   jump fixup_done
   
tag_ref_list:
   call_vn __zml_ref_list_fixup_pointers block table table_dwords

fixup_done:
   call_2s __zml_allocated_block_size block -> sp
   add block sp -> block
   jump traverse_compacted

end_traversal:
   ; now fixup pointers in the roots table
   call_2s __zml_freelist_node_size freelist_end -> sp
   add freelist_end sp -> roots_table_boundary

   sub roots_table_boundary 1 -> block
check_next_root:
   inc 'block
   jeq block HEAP_WORDS ?end_roots_table                       ; jump if roots table has been traversed
   loadw __heap_start block -> tag
   jeq tag LIST_NULL ?check_next_root                          ; jump if this is end-of-freelist
   jl tag roots_table_boundary ?is_heap_ref                    ; jump if this is a heap pointer and not a freelist entry
   jump check_next_root

is_heap_ref:
   call_vn __zml_fixup_pointer block table table_dwords
   jump check_next_root

end_roots_table:
   rtrue


.FUNCT __zml_bisect_fixup_table, table, table_dwords, pointer, lower, upper, mid
   ; Given a heap pointer, determine which break table entry should be used to
   ; adjust its value.
   ;
   ; param table: word address where break table begins (heap relative)
   ; param table_dwords: length of break table, in double-words
   ; param pointer: heap pointer to be adjusted
   ; local lower: lower bound on table index
   ; local upper: upper bound on table index
   ; local mid: bisection location
   ;
   ; Returns: dword index of last table entry such that (pointer >= table entry),
   ;          or -1 if the pointer is smaller than all table entries
   
   jz table_dwords ?return_no_match             ; jump if table is empty
   loadw __heap_start table -> sp
   jl pointer sp ?return_no_match               ; jump if pointer is smaller than first table entry

   store 'lower 0
   store 'upper table_dwords                    ; (using half-open interval arithmetic)

   mul table 2 -> table
   add __heap_start table -> table              ; convert table to a byte array address, for use with loadw

bisect:
   sub upper lower -> sp
   jeq sp 1 ?bisect_done                        ; jump if bisection range has been reduced to one element
   add lower upper -> mid
   div mid 2 -> mid                             ; "mid" as dword
   mul mid 2 -> sp                              ; "mid" as word
   loadw table sp -> sp                         ; lookup pointer value in table
   jl pointer sp ?below_mid                     ; jump if pointer value is in bottom half
   load 'mid -> lower                           ; closed interval--"lower" is <= the pointer
   jump bisect

below_mid:
   load 'mid -> upper                           ; open interval--"upper" is strictly > the pointer
   jump bisect

bisect_done:
   ret lower

return_no_match:
   ret -1


.FUNCT __zml_test_bisect, table, table_dwords, i
   store 'table 16
   load 'table -> i

   storew __heap_start i 1
   inc 'i
   storew __heap_start i 0
   inc 'i

   storew __heap_start i 2
   inc 'i
   storew __heap_start i 0
   inc 'i

   storew __heap_start i 5
   inc 'i
   storew __heap_start i 0
   inc 'i

   storew __heap_start i 8 
   inc 'i
   storew __heap_start i 0
   inc 'i

   storew __heap_start i 100 
   inc 'i
   storew __heap_start i 0
   inc 'i

   storew __heap_start i 101 
   inc 'i
   storew __heap_start i 0
   inc 'i

   sub i table -> table_dwords
   div table_dwords 2 -> table_dwords

   call_vs __zml_bisect_fixup_table table table_dwords 0 -> sp
   print "expected -1, got "
   print_num sp
   new_line

   call_vs __zml_bisect_fixup_table table table_dwords 1 -> sp
   print "expected 0, got "
   print_num sp
   new_line

   call_vs __zml_bisect_fixup_table table table_dwords 2 -> sp
   print "expected 1, got "
   print_num sp
   new_line

   call_vs __zml_bisect_fixup_table table table_dwords 6 -> sp
   print "expected 2, got "
   print_num sp
   new_line

   call_vs __zml_bisect_fixup_table table table_dwords 50 -> sp
   print "expected 3, got "
   print_num sp
   new_line

   call_vs __zml_bisect_fixup_table table table_dwords 101 -> sp
   print "expected 5, got "
   print_num sp
   new_line

   call_vs __zml_bisect_fixup_table table table_dwords 102 -> sp
   print "expected 5, got "
   print_num sp
   new_line

   call_vs __zml_bisect_fixup_table table table_dwords 1000 -> sp
   print "expected 5, got "
   print_num sp
   new_line

   rtrue


.FUNCT __zml_fixup_pointer, pointer_addr, table, table_dwords, pointer_val
   ; Given a break table and the address of a  pointer to be adjusted,
   ; updates the pointer in-place.
   ;
   ; param pointer_addr: word address containing a pointer (heap-relative)
   ; param table: word address where break table begins (heap relative)
   ; param table_dwords: length of break table, in double-words
   ; local pointer_val: value stored at pointer_addr
   loadw __heap_start pointer_addr -> pointer_val
   call_vs __zml_bisect_fixup_table table table_dwords pointer_val -> sp
   load 'sp -> sp                                     ; duplicate stack value (table index)
   jeq sp -1 ?no_fixup                                ; jump if no fixup required

   ; compute heap-relative address of break table adjustment value
   mul sp 2 -> sp
   add table sp -> sp
   inc 'sp

   ; apply adjustment to pointer value
   loadw __heap_start sp -> sp
   sub pointer_val sp -> pointer_val
   storew __heap_start pointer_addr pointer_val

no_fixup:
   rtrue


.FUNCT __zml_tag_get, ref
   ; Retrieve the value of the tag for the given block.
   ;
   ; param ref: word index of start of the block (heap-relative)
   ;
   ; Returns: tag value
   loadw __heap_start ref -> sp
   and sp TAG_MASK -> sp
   ret_popped


.FUNCT __zml_alloc_block, size_words, curr_node, prev_node, next_node, node_size, is_swept, is_compacted
   ; Allocate a block of the given size, which shall be an even nonzero value.  If
   ; unsuccessful, the program is aborted with an "out of memory" message.
   ;
   ; param size_words: size of block to be allocated, in words; must be even and >= 2.
   ; local prev_node: pointer to previous freelist node, or FREELIST_INVALID
   ; local curr_node: pointer to current freelist node
   ; local next_node: pointer to next freelist node, or FREELIST_INVALID
   ; local node_size: stores size of a node
   ; local is_swept: true if heap has already been swept
   ; local is_compacted: true if heap has already been compacted
   ;
   ; Returns: word index where block begins (heap-relative)
   store 'is_swept 0
   store 'is_compacted 0

start_alloc:
   jeq freelist_head LIST_NULL ?end_of_list             ; jump if zero memory available
   store 'prev_node LIST_NULL
   load 'freelist_head -> curr_node
   call_2s __zml_freelist_node_next curr_node -> next_node
   
try_alloc_node:
   ; preconditions: prev_node, curr_node, next_node all set
   call_2s __zml_freelist_node_size curr_node -> node_size  ; size of current freelist node
   jl node_size size_words ?move_next_node                  ; jump if not enough space to alloc
   jeq node_size size_words ?alloc_entire_node              ; jump if entire node is consumed

   ; divide curr_node into two pieces: an region to be allocated and a new freelist node
   call_vn __zml_freelist_node_divide curr_node size_words
   call_2s __zml_freelist_node_next curr_node -> next_node  ; update next_node to reflect change

alloc_entire_node:
   jeq curr_node freelist_end ?end_of_list                  ; jump if this would eliminate the last freelist node
   call_vn __zml_freelist_node_remove prev_node next_node   ; drop curr_node from freelist
   ret curr_node

move_next_node:
   load 'curr_node -> prev_node
   load 'next_node -> curr_node
   jeq curr_node LIST_NULL ?end_of_list                     ; jump if last node
   call_2s __zml_freelist_node_next curr_node -> next_node  ; lookup next-node pointer
   jump try_alloc_node

end_of_list:
   jeq is_swept 1 ?compact_heap                             ; jump if we already tried sweeping the heap to free memory
   call_1n __zml_mark_roots
   call_1n __zml_sweep
   store 'is_swept 1
   jump start_alloc

compact_heap:
   jeq is_compacted 1 ?out_of_memory                        ; jump if we already tried compacting the heap to free memory
   call_1n __zml_compact
   store 'is_compacted 1
   jump start_alloc

out_of_memory:
   print "Out of memory."
   new_line
   quit


.FUNCT __zml_freelist_node_remove, prev_node, next_node
   ; Remove a node from the freelist.
   ;
   ; param prev_node: pointer to previous node in freelist, or LIST_NULL
   ; param next_node: pointer to next node in freelist, or LIST_NULL
   jeq prev_node LIST_NULL ?remove_freelist_head                 ; jump if this is first node in freelist
   call_vn __zml_freelist_node_set_next prev_node next_node      ; prev_node now linked to next_node
   rtrue

remove_freelist_head:
   store 'freelist_head next_node
   rtrue


.FUNCT __zml_freelist_node_divide, node, size_words, new_node
   ; Divides a freelist node into two pieces.
   ;
   ; param node: pointer to node of size >= size_words + 2
   ; param size_words: desired size of first node
   ; local new_node: location of newly created node
   add node size_words -> new_node                             ; set location of new node
   call_2s __zml_freelist_node_next node -> sp                 ; push location of next node
   call_2s __zml_freelist_node_size node -> sp
   sub sp size_words -> sp                                     ; push size of new node
   call_vn __zml_freelist_node_cons new_node sp sp             ; create new node linked to next_node
   call_vn __zml_freelist_node_cons node size_words new_node   ; link old node to new one
   jeq node freelist_end ?update_freelist_end                  ; jump if divided node was end-of-list
   rtrue

update_freelist_end:
   store 'freelist_end new_node
   rtrue


.FUNCT __zml_freelist_node_cons, node, size_words, next
   ; Constructs a new freelist node.
   ;
   ; param node: word pointer to node (even)
   ; param size_words: number of words in node (even)
   ; param next: word pointer to next node (even), or LIST_NULL
   or size_words FREELIST_BIT -> sp
   storew __heap_start node sp
   inc 'node
   storew __heap_start node next
   rtrue


.FUNCT __zml_freelist_node_size, node
   ; Returns: size of the given freelist node, in words.
   loadw __heap_start node -> sp          ; sp contains freelist node header
   and sp FREELIST_SIZE_MASK -> sp        ; sp contains size word
   ret_popped


.FUNCT __zml_freelist_node_next, node
   ; Returns: next node in the freelist.  Value 0 means end-of-list.
   inc 'node
   loadw __heap_start node -> node
   ret node


.FUNCT __zml_freelist_node_set_next, node, next
   ; Sets the "next node" pointer in freelist entry <node> to the value <next>.
   inc 'node
   storew __heap_start node next
   rtrue


.FUNCT zml_register_root, heap_ref, root, size, is_compacted
   ; Creates a new entry in the table of GC roots.
   ;
   ; param heap_ref: word pointer to a heap-allocated block which is to be
   ;     registered as a root (heap relative)
   ; local root: new root value
   ; local size: stores size of a heap freelist entry
   ; local is_compacted: true if heap has been compacted
   ;
   ; Returns: unique root identifier.  The root identifier is a heap-relative word
   ;     pointer which, when dereferenced, yields the current location of the
   ;     heap-allocated block.
   ;
   ; Implementation note: by design, the root freelist is never allowed to be
   ; empty.  This ensures that we always have a place to store heap_ref inside the
   ; roots table.  To satisfy that requirement, this function must ensure that
   ; if the *last* root entry is allocated, then the table must be grown before
   ; the function exits.  It may be necessary to compact the heap in order to
   ; grow the table--and it will then be safe to perform the compaction, because the
   ; heap_ref will have already been successfully registered at that time.
   
   store 'is_compacted 0
   load 'root_freelist_head -> root
   loadw __heap_start root_freelist_head -> root_freelist_head    ; allocate root from the freelist
   storew __heap_start root heap_ref                              ; register the root
   jeq root_freelist_head LIST_NULL ?empty_freelist               ; jump if the freelist is now empty
   ret root

empty_freelist:
   ; we allocate two words at a time, to maintain dword alignment of heap
   call_2s __zml_freelist_node_size freelist_end -> size
   jl size 4 ?compact_memory                                      ; jump if there is not enough room at the end of heap memory
   sub size 2 -> size
   call_vn __zml_freelist_node_cons freelist_end size LIST_NULL   ; resize the last heap freelist entry
   add freelist_end size -> root_freelist_head                    ; the words following the heap freelist now become a root
   add root_freelist_head 1 -> sp                                 ;     freelist of size 2
   storew __heap_start root_freelist_head sp
   add root_freelist_head 1 -> sp
   storew __heap_start sp LIST_NULL
   ret root

compact_memory:
   jeq is_compacted 1 ?out_of_memory                              ; jump if heap was already compacted
   call_1n __zml_mark_roots
   call_1n __zml_sweep
   call_1n __zml_compact
   store 'is_compacted 1
   jump empty_freelist                                            ; check if we have enough memory now

out_of_memory:
   print "Out of memory."
   new_line
   quit


.FUNCT zml_unregister_root, root_ref
   ; Unregister a root reference which had been obtained from zml_register_root.
   ;
   ; param root_ref: root reference to be dropped from the GC roots table
   storew __heap_start root_ref root_freelist_head
   store 'root_freelist_head root_ref
   rtrue


.FUNCT __zml_mark_roots, i, roots_table_boundary, heap_ref
   ; Recursively mark all heap memory which is reachable through entries in
   ; the table of roots.
   ;
   ; local i: counter
   ; local roots_table_boundary: any pointers >= this address are root freelist
   ;     entries; otherwise they are heap pointers to be marked
   ; local heap_ref: heap reference to be marked
   call_2s __zml_freelist_node_size freelist_end -> sp
   add freelist_end sp -> roots_table_boundary

   load 'roots_table_boundary -> i
check_next_root:
   jeq i HEAP_WORDS ?end_roots_table                           ; jump if roots table has been traversed
   loadw __heap_start i -> heap_ref
   inc 'i
   jeq heap_ref LIST_NULL ?check_next_root                     ; jump if this is end-of-freelist
   jl heap_ref roots_table_boundary ?is_heap_ref               ; jump if this is a heap pointer and not a freelist entry
   jump check_next_root

is_heap_ref:
   call_vn __zml_mark_recursive heap_ref 1
   jump check_next_root

end_roots_table:
   rtrue


.FUNCT zml_print_int, i
	 ; Prints an integer, using decimal notation.
	 ;
	 ; param i: value to be printed
	 print_num i
	 rtrue


.FUNCT zml_print_newline, unit
 	 ; Prints a newline character.
	 ;
	 ; param unit: receives value 0 as the unit argument
	 new_line
	 rtrue


; User code goes here.  It shall define the entry point "zml_main",
; which is invoked without arguments from __zml_main .
.INSERT "program.zap"

.END
