; Z-machine header, 64 bytes
; "Zapf"  ==> assembler will set the value
; "Reset" ==> interpreter will set the value
.BYTE 5                   ;  0:   Zapf: Z-machine version 5
.BYTE 0                   ;  1:   Reset: flags 1
.WORD 0                   ;  2:   (Reserved)
.WORD __begin_high        ;  4:   Base of high memory
.WORD __zml_main          ;  6:   Initial value of PC
.WORD 0                   ;  8:   Byte address of dictionary
.WORD 0                   ;  A:   Byte address of object table
.WORD __begin_globals     ;  C:   Byte address of global variables table
.WORD __begin_static      ;  E:   Base of static memory
.WORD 0                   ; 10:   Reset: flags 2
.WORD 0                   ; 12:   (Reserved)
.WORD 0                   ; 14:   (Reserved)
.WORD 0                   ; 16:   (Reserved)
.WORD 0                   ; 18:   Byte address of abbreviations table
.WORD 0                   ; 1A:   Zapf: Length of file
.WORD 0                   ; 1C:   Zapf: Checksum of file
.WORD 0                   ; 1E:   Reset: Interpreter version
.WORD 0                   ; 20:   Reset: Screen dimensions
.WORD 0                   ; 22;   Reset: Graphical screen width (set by interpreter)
.WORD 0                   ; 24;   Reset: Graphical screen height (set by interpreter)
.WORD 0                   ; 26:   Reset: font dimensions
.WORD 0                   ; 28:   Routines offset / 8
.WORD 0                   ; 2A:   Static strings offset / 8
.WORD 0                   ; 2C:   Reset: color scheme
.WORD 0                   ; 2E:   Byte address of terminating characters table
.WORD 0                   ; 30:   Width in pixels of text sent to output stream
.WORD 0                   ; 32:   Reset: revision number
.WORD 0                   ; 34:   Select default alphabet table
.WORD 0                   ; 36:   Disable header extension table
.WORD 0                   ; 38:   (Padding)
.WORD 0                   ; 3A:   (Padding)
.WORD 0                   ; 3C:   Zapf: "ZA"
.WORD 0                   ; 3E:   Zapf: "PF"

__header_end::
.ENDI

