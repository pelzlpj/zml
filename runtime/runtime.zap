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
FREELIST_HEADER=HEAP_WORDS+32768

; Beginning of heap memory is at byte offset 0x220=544.  At program start, the
; heap is  just a free list with a single entry.
__heap_start::
.WORD FREELIST_HEADER    ; Free list cons cell containing 'HEAP_WORDS' free
.WORD 0                  ; Last entry in list

; Insert zeros for the empty space until end of dynamic area
.INSERT "empty_heap.zap"

__begin_static::
__begin_high::

__zml_main::
   print "hello, world!"
   new_line
   quit

.END
