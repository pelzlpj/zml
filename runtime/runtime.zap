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

MARK_BIT=16384       ; Second-highest bit is the mark bit
NOT_MARK_BIT=49151
TAG_MASK=31          ; Low-order five bits hold the type tag

VALUEWORD_TAG=0   ; Header word for a value word cell
REFWORD_TAG=1     ; Header word for a reference word cell
VALUEARRAY_TAG=2  ; Header word for a value array cell
REFARRAY_TAG=3    ; Header word for a reference array cell
VALUELIST_TAG=4   ; Header word for a value list cell
REFLIST_TAG=5     ; Header word for a reference list cell



; Insert zeros for the empty space until end of dynamic area
__heap_start::
.INSERT "empty_heap.zap"

__begin_static::
__begin_high::

__zml_main::
   call_1n __zml_init_heap
   call_1n __main
   quit


.FUNCT __main, ref1, ref2
   call_vs zml_alloc_value_word 1 -> ref1
   call_vs zml_alloc_ref_list ref1 LIST_NULL -> ref1
   call_vs zml_alloc_value_word 2 -> ref2          ; should not be marked, because parent not marked
   call_vs zml_alloc_ref_list ref2 ref1 -> ref2    ; should not be marked, has no parent
   call_vs zml_alloc_ref_array 1 ref1 -> ref1
   call_vn __zml_mark_recursive ref1 1
   save -> sp
   rtrue
   

.FUNCT __zml_init_heap
   ; Initialize the heap with zero words allocated.  We end up with
   ; a freelist with one entry representing the entire heap.
   call_vn __zml_freelist_node_cons 0 HEAP_WORDS LIST_NULL
   store 'freelist_head 0
   store 'freelist_end  0
   rtrue


.FUNCT zml_alloc_value_word, init_val, ref
   ; Allocate a word cell which stores a single word by value.
   ; 
   ; param init_val: the initial value to be stored
   ; local ref: the location of the reference cell
   ;
   ; Returns: word index where value word cell begins (heap-relative)
   call_2s __zml_alloc_block 2 -> ref
   storew __heap_start ref VALUEWORD_TAG
   add ref 1 -> sp
   storew __heap_start sp init_val
   ret ref


.FUNCT zml_alloc_ref_word, init_val, ref
   ; Allocate a word cell which stores a single reference (pointer).
   ; 
   ; param init_val: the initial value to be stored
   ; local ref: the location of the reference cell
   ;
   ; Returns: word index where reference word cell begins (heap-relative)
   call_2s __zml_alloc_block 2 -> ref
   storew __heap_start ref REFWORD_TAG
   add ref 1 -> sp
   storew __heap_start sp init_val
   ret ref


.FUNCT zml_word_get, ref
   ; Retrieve the value stored in a word reference cell.
   ;
   ; param ref: word index where word cell begins (heap-relative)
   ;
   ; Returns: value
   inc 'ref
   loadw __heap_start ref -> sp
   ret_popped


.FUNCT zml_word_set, ref, val
   ; Set the value stored in a word reference cell.
   ;
   ; param ref: word index where word cell begins (heap-relative)
   ; param val: new value to place in cell
   inc 'ref
   storew __heap_start ref val
   rtrue


.FUNCT __zml_word_mark_children, ref, is_set
   ; Recursively set or clear the 'mark' bit on all children belonging to
   ; this word cell.
   ;
   ; param ref: word index where word cell begins (heap-relative)
   ; param is_set: 1 if mark should be set, 0 if cleared
   inc 'ref
   call_vn __zml_mark_recursive ref is_set
   rtrue


NOT_ONE=65534  ; bitwise not of 1

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


.FUNCT __zml_alloc_array, size, init_val, header_word, curr_word
   ; Allocate a new array of the given size, applying the specified ; array header
   ; to the reference cell. The initial value is assigned to all elements.
   ;
   ; param size: length of the array >= 0, in words
   ; param init_val: initial value to store in all locations
   ; param header_word: word to be placed in the array header
   ; local curr_word: current word being written
   ;
   ; Returns: word index where array begins (heap-relative)
   add size 3 -> sp
   and sp NOT_ONE -> sp                      ; even size ==> sp = size+2; odd size ==> sp = size+3
   call_2s __zml_alloc_block sp -> sp        ; sp contains array ref
   load 'sp -> curr_word
   storew __heap_start curr_word header_word
   inc 'curr_word
   storew __heap_start curr_word size

fill_words:
   jz size ?done                             ; jump if size is zero
   inc 'curr_word
   storew __heap_start curr_word init_val
   dec 'size
   jump fill_words

done:
   ret_popped


.FUNCT zml_array_size, arr
   ; Retrieve the size of the specified array.
   ;
   ; param arr: word index where array begins (heap-relative)
   ;
   ; Returns: array size
   inc 'arr
   loadw __heap_start arr -> sp
   ret_popped


.FUNCT zml_array_get, arr, index
   ; Retrieve the value stored in the array at the given index.
   ;
   ; param arr: word index where array begins (heap-relative)
   ; param index: array value to retrieve; 0 <= index < array size
   ;
   ; Returns: array value
   add arr 2 -> sp
   add sp index -> sp
   loadw __heap_start sp -> sp
   ret_popped


.FUNCT zml_array_set, arr, index, val
   ; Set the value stored in the array at the given index.
   ;
   ; param arr: word index where array begins (heap-relative)
   ; param index: array value to set; 0 <= word < array size
   ; param val: word to place in array
   add arr 2 -> sp
   add sp index -> sp
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
   jeq tag REFWORD_TAG     ?ref_word
   jeq tag REFARRAY_TAG    ?ref_array
   jeq tag VALUELIST_TAG   ?value_list
   jeq tag REFLIST_TAG     ?ref_list
   rtrue                                  ; default case: no pointers to children

already_marked:
   rtrue

ref_word:
   call_vn __zml_word_mark_children ref is_set
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


.FUNCT __zml_tag_get, ref
   ; Retrieve the value of the tag for the given block.
   ;
   ; param ref: word index of start of the block (heap-relative)
   ;
   ; Returns: tag value
   loadw __heap_start ref -> sp
   and sp TAG_MASK -> sp
   ret_popped


.FUNCT __zml_alloc_block, size_words, curr_node, prev_node, next_node, node_size
   ; Allocate a block of the given size, which shall be an even nonzero value.  If
   ; unsuccessful, the program is aborted with an "out of memory" message.
   ;
   ; param size_words: size of block to be allocated, in words; must be even and >= 2.
   ; local prev_node: pointer to previous freelist node, or FREELIST_INVALID
   ; local curr_node: pointer to current freelist node
   ; local next_node: pointer to next freelist node, or FREELIST_INVALID
   ; local node_size: stores size of a node
   ;
   ; Returns: word index where block begins (heap-relative)
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
   call_vn __zml_freelist_node_remove prev_node next_node   ; drop curr_node from freelist
   ret curr_node

move_next_node:
   load 'curr_node -> prev_node
   load 'next_node -> curr_node
   jeq curr_node LIST_NULL ?end_of_list                 ; jump if last node
   call_2s __zml_freelist_node_next curr_node -> next_node  ; lookup next-node pointer
   jump try_alloc_node

end_of_list:
   print "Out of memory."
   new_line
   quit


.FUNCT __zml_freelist_node_remove, prev_node, next_node
   ; Remove a node from the freelist.
   ;
   ; param prev_node: pointer to previous node in freelist, or LIST_NULL
   ; param next_node: pointer to next node in freelist, or LIST_NULL
   jeq prev_node LIST_NULL ?remove_freelist_head                 ; jump if this is first node in freelist
   call_vn __zml_freelist_node_set_next prev_node next_node          ; prev_node now linked to next_node
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

   
.END
