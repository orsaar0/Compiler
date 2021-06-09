%define T_UNDEFINED 0
%define T_VOID 1
%define T_NIL 2
%define T_RATIONAL 3
%define T_FLOAT 4
%define T_BOOL 5
%define T_CHAR 6
%define T_STRING 7
%define T_SYMBOL 8
%define T_CLOSURE 9
%define T_PAIR 10

%define TYPE_SIZE 1
%define WORD_SIZE 8
	
%define KB(n) n*1024
%define MB(n) 1024*KB(n)
%define GB(n) 1024*MB(n)


%macro SKIP_TYPE_TAG 2
	mov %1, qword [%2+TYPE_SIZE]	
%endmacro	

%define NUMERATOR SKIP_TYPE_TAG

%macro DENOMINATOR 2
	mov %1, qword [%2+TYPE_SIZE+WORD_SIZE]
%endmacro

%macro CHAR_VAL 2
	movzx %1, byte [%2+TYPE_SIZE]
%endmacro

%define FLOAT_VAL SKIP_TYPE_TAG

%define STRING_LENGTH SKIP_TYPE_TAG

%define SYMBOL_VAL SKIP_TYPE_TAG

%macro STRING_ELEMENTS 2
	lea %1, [%2+TYPE_SIZE+WORD_SIZE]
%endmacro

%define CAR SKIP_TYPE_TAG

%macro CDR 2
	mov %1, qword [%2+TYPE_SIZE+WORD_SIZE]
%endmacro

%define CLOSURE_ENV CAR

%define CLOSURE_CODE CDR

%define PVAR(n) qword [rbp+(4+n)*WORD_SIZE]

; returns %2 allocated bytes in register %1
; Supports using with %1 = %2
%macro MALLOC 2
	add qword [malloc_pointer], %2
	push %2
	mov %1, qword [malloc_pointer]
	sub %1, [rsp]
	add rsp, 8
%endmacro

%define PARAM_COUNT qword [rbp+3*WORD_SIZE]

%define SHIFT_PARAM PARAM_COUNT+5
; on enterance rbx <- vector of size extEnv*WS
; r13 <- extEnvSize
; on exit: rbx <- updated extEnv 
%macro EXT_ENV 0
	mov rcx, PARAM_COUNT	; rcx <- argc
	inc rcx					; for the magic
	shl rcx, 3				; rcx <- rcx*WORD_SIZE
	MALLOC rdx, rcx			; rdx <- vector of size argc*WS, newParamVector
	mov [rbx], rdx			; extEnv[0] <- rdx
	
	mov r9, PARAM_COUNT		; r9 <- argc
	inc r9					; for the magic
	mov rcx, 0				; rcx is the running index
%%create_param_vector_loop:	
	cmp rcx, r9								; if index == argc -->> end of params (no param of index [argc])
	je %%end_param_loop

	add rcx, 4							
	lea r10, [rbp + WORD_SIZE * rcx]
	mov r10, [r10]							; r10 <- param num. rcx 
	sub rcx, 4
	mov [rdx + (WORD_SIZE * rcx)], r10			; newParamVector[rcx] <- r10
	add rcx, 1
	jmp %%create_param_vector_loop

%%end_param_loop:	
	mov r12, qword [rbp +WORD_SIZE * 2]		; r12 <- pointer of currEnv 
	sub r13, 1								; currEnvSize == extEnvSize -1
	mov rcx, r13							; rcx <- (currEnv size)
%%copy_pointers_from_env_to_extenv_loop:
	cmp rcx, 0
	jz %%end
	mov r8, rcx					; r8 <- currEnvSize- number of arguments that were copied
	sub r8, 1 					; r8 <- the running index of the currEnv
	lea r11, [r12 + r8*WORD_SIZE]
	mov r11, [r11]					; r11 <- address of currEnv[r8]
	;mov r11, [r12 + r8*WORD_SIZE]	; r11 <- address of currEnv[r8]
	add r8, 1
	mov [rbx + WORD_SIZE * r8] , r11	;extEnv[r8+1] <- currEnv[r8]
	sub rcx, 1						; loop with r8-1
	jmp %%copy_pointers_from_env_to_extenv_loop	
%%end:

%endmacro

%macro SHIFT_FRAME 1 
; %1 = size of frame(constant)
	push rax
	mov rax, PARAM_COUNT
	add rax, 5
	shl rcx, 3
	mov rcx, rax			; rcx <- (PARAM_COUNT+5)*WORD_SIZE in order to inc the rdp later
%assign i 1
%rep %1
	dec rax
	push qword [rbp-i*WORD_SIZE]
	pop qword [rbp+rax*WORD_SIZE]
%assign i i+1
%endrep
	pop rax
	add rsp, rcx		; inc the rsp to the new frame
%endmacro

%define PARAM_COUNT_OPT qword [rbp+WORD_SIZE*2]

; %1 number of args need to be packed 
; %2 the vector offset (one before magic)
; %3 number of minimum args (constant)
%macro PACK_OPT_ARGS 3
	mov rcx, 0
	mov rdx, SOB_NIL_ADDRESS
	%%pack_loop:
		cmp rcx, %1
		je %%end_pack_loop
		
		mov r11, %2
		sub r11, rcx

		lea r10, [r15 + WORD_SIZE*r11]		; last arg is first
		mov r10, [r10]

		MAKE_PAIR (rbx, r10, rdx)
		mov rdx, rbx
		
		inc rcx
		jmp %%pack_loop
	%%end_pack_loop:	
	lea r10, [r15 + WORD_SIZE * %2]
	mov qword [r10], rbx					; last legal arg on stack <- pointer to args vector
	
%endmacro

; %1 shifting amount - number of args packed-1
; %2-1 offset of first arg to shift - A[n] (= minimum args+3) (constant)
; shifting the rest of the frame (below the vector) %1*WS up
%macro ADJUST_FRAME 2
	%assign i %2-1
	%%loopi:
	%rep %2
		mov r12, qword [r15 + WORD_SIZE*i]		
		lea r11, [r15 + WORD_SIZE*(i + %1)] 
		mov qword [r11], r12
	%assign i i-1
	%endrep
	shl %1, 3
	add r15, %1				; shifting rsp up
%endmacro
	
; Creates a short SOB with the
; value %2
; Returns the result in register %1
%macro MAKE_CHAR_VALUE 2
	MALLOC %1, 1+TYPE_SIZE
	mov byte [%1], T_CHAR
	mov byte [%1+TYPE_SIZE], %2
%endmacro

; Creates a long SOB with the
; value %2 and type %3.
; Returns the result in register %1
%macro MAKE_LONG_VALUE 3
	MALLOC %1, TYPE_SIZE+WORD_SIZE
	mov byte [%1], %3
	mov qword [%1+TYPE_SIZE], %2
%endmacro

%define MAKE_FLOAT(r,val) MAKE_LONG_VALUE r, val, T_FLOAT
%define MAKE_CHAR(r,val) MAKE_CHAR_VALUE r, val

; Create a string of length %2
; from char %3.
; Stores result in register %1
%macro MAKE_STRING 3
	lea %1, [%2+WORD_SIZE+TYPE_SIZE]
	MALLOC %1, %1
	mov byte [%1], T_STRING
	mov qword [%1+TYPE_SIZE], %2
	push rcx
	add %1,WORD_SIZE+TYPE_SIZE
	mov rcx, %2
	cmp rcx, 0
%%str_loop:
	jz %%str_loop_end
	dec rcx
	mov byte [%1+rcx], %3
	jmp %%str_loop
%%str_loop_end:
	pop rcx
	sub %1, WORD_SIZE+TYPE_SIZE
%endmacro

;;; Creates a SOB with tag %2 
;;; from two pointers %3 and %4
;;; Stores result in register %1
%macro MAKE_TWO_WORDS 4 
        MALLOC %1, TYPE_SIZE+WORD_SIZE*2
        mov byte [%1], %2
        mov qword [%1+TYPE_SIZE], %3
        mov qword [%1+TYPE_SIZE+WORD_SIZE], %4
%endmacro

%macro MAKE_WORDS_LIT 3
	db %1
        dq %2
        dq %3
%endmacro

%define MAKE_RATIONAL(r, num, den) \
	MAKE_TWO_WORDS r, T_RATIONAL, num, den

%define MAKE_LITERAL_RATIONAL(num, den) \
	MAKE_WORDS_LIT T_RATIONAL, num, den
	
%define MAKE_PAIR(r, car, cdr) \
        MAKE_TWO_WORDS r, T_PAIR, car, cdr

%define MAKE_LITERAL_PAIR(car, cdr) \
        MAKE_WORDS_LIT T_PAIR, car, cdr

%define MAKE_CLOSURE(r, env, body) \
        MAKE_TWO_WORDS r, T_CLOSURE, env, body

%macro MAKE_LITERAL 2 
;Make a literal of type %1; followed by the definition %2
	db %1
	%2
%endmacro

%define MAKE_LITERAL_FLOAT(val) MAKE_LITERAL T_FLOAT, dq val
%define MAKE_LITERAL_CHAR(val) MAKE_LITERAL T_CHAR, db val
%define MAKE_LITERAL_SYMBOL(val) MAKE_LITERAL T_SYMBOL, dq val

%macro MAKE_LITERAL_STRING 1
	db T_STRING
	dq (%%end_str - %%str)
	%%str:
	db %1
	%%end_str:
%endmacro


;;; Macros and routines for printing Scheme OBjects to STDOUT
%define CHAR_NUL 0
%define CHAR_TAB 9
%define CHAR_NEWLINE 10
%define CHAR_PAGE 12
%define CHAR_RETURN 13
%define CHAR_SPACE 32
%define CHAR_DOUBLEQUOTE 34
%define CHAR_BACKSLASH 92
	
extern printf, malloc
global write_sob, write_sob_if_not_void
	
write_sob_undefined:
	push rbp
	mov rbp, rsp

	mov rax, qword 0
	mov rdi, .undefined
	call printf

	pop rbp
	ret

section .data
.undefined:
	db "#<undefined>", 0

write_sob_rational:
	push rbp
	mov rbp, rsp

	mov rdx, rsi
	NUMERATOR rsi, rdx
	DENOMINATOR rdx, rdx
	
	cmp rdx, 1
	jne .print_fraction

	mov rdi, .int_format_string
	jmp .print

.print_fraction:
	mov rdi, .frac_format_string

.print:	
	mov rax, 0
	call printf

	pop rbp
	ret

section .data
.int_format_string:
	db "%ld", 0
.frac_format_string:
	db "%ld/%ld", 0

write_sob_float:
	push rbp
	mov rbp, rsp

	FLOAT_VAL rsi, rsi
	movq xmm0, rsi
	mov rdi, .float_format_string
	mov rax, 1

	;; printf-ing floats (among other things) requires the stack be 16-byte aligned
	;; so align the stack downwards (take up some extra space) if needed before
	;; calling printf for floats
	and rsp, -16 
	call printf

	;; move the stack back to the way it was, cause we messed it up in order to
	;; call printf.
	;; Note that the `leave` instruction does exactly this (reset the stack and pop
	;; rbp). The instructions are explicitly layed out here for clarity.
	mov rsp, rbp
	pop rbp
	ret
	
section .data
.float_format_string:
	db "%f", 0		

write_sob_char:
	push rbp
	mov rbp, rsp

	CHAR_VAL rsi, rsi

	cmp rsi, CHAR_NUL
	je .Lnul

	cmp rsi, CHAR_TAB
	je .Ltab

	cmp rsi, CHAR_NEWLINE
	je .Lnewline

	cmp rsi, CHAR_PAGE
	je .Lpage

	cmp rsi, CHAR_RETURN
	je .Lreturn

	cmp rsi, CHAR_SPACE
	je .Lspace
	jg .Lregular

	mov rdi, .special
	jmp .done	

.Lnul:
	mov rdi, .nul
	jmp .done

.Ltab:
	mov rdi, .tab
	jmp .done

.Lnewline:
	mov rdi, .newline
	jmp .done

.Lpage:
	mov rdi, .page
	jmp .done

.Lreturn:
	mov rdi, .return
	jmp .done

.Lspace:
	mov rdi, .space
	jmp .done

.Lregular:
	mov rdi, .regular
	jmp .done

.done:
	mov rax, 0
	call printf

	pop rbp
	ret

section .data
.space:
	db "#\space", 0
.newline:
	db "#\newline", 0
.return:
	db "#\return", 0
.tab:
	db "#\tab", 0
.page:
	db "#\page", 0
.nul:
	db "#\nul", 0
.special:
	db "#\x%02x", 0
.regular:
	db "#\%c", 0

write_sob_void:
	push rbp
	mov rbp, rsp

	mov rax, 0
	mov rdi, .void
	call printf

	pop rbp
	ret

section .data
.void:
	db "#<void>", 0
	
write_sob_bool:
	push rbp
	mov rbp, rsp

	cmp word [rsi], word T_BOOL
	je .sobFalse
	
	mov rdi, .true
	jmp .continue

.sobFalse:
	mov rdi, .false

.continue:
	mov rax, 0
	call printf	

	pop rbp
	ret

section .data			
.false:
	db "#f", 0
.true:
	db "#t", 0

write_sob_nil:
	push rbp
	mov rbp, rsp

	mov rax, 0
	mov rdi, .nil
	call printf

	pop rbp
	ret

section .data
.nil:
	db "()", 0

write_sob_string:
	push rbp
	mov rbp, rsp

	push rsi

	mov rax, 0
	mov rdi, .double_quote
	call printf
	
	pop rsi

	STRING_LENGTH rcx, rsi
	STRING_ELEMENTS rax, rsi

.loop:
	cmp rcx, 0
	je .done
	mov bl, byte [rax]
	and rbx, 0xff

	cmp rbx, CHAR_TAB
	je .ch_tab
	cmp rbx, CHAR_NEWLINE
	je .ch_newline
	cmp rbx, CHAR_PAGE
	je .ch_page
	cmp rbx, CHAR_RETURN
	je .ch_return
	cmp rbx, CHAR_DOUBLEQUOTE
	je .ch_doublequote
	cmp rbx, CHAR_BACKSLASH
	je .ch_backslash
	cmp rbx, CHAR_SPACE
	jl .ch_hex
	
	mov rdi, .fs_simple_char
	mov rsi, rbx
	jmp .printf
	
.ch_hex:
	mov rdi, .fs_hex_char
	mov rsi, rbx
	jmp .printf
	
.ch_tab:
	mov rdi, .fs_tab
	mov rsi, rbx
	jmp .printf
	
.ch_page:
	mov rdi, .fs_page
	mov rsi, rbx
	jmp .printf
	
.ch_return:
	mov rdi, .fs_return
	mov rsi, rbx
	jmp .printf

.ch_newline:
	mov rdi, .fs_newline
	mov rsi, rbx
	jmp .printf

.ch_doublequote:
	mov rdi, .fs_doublequote
	mov rsi, rbx
	jmp .printf

.ch_backslash:
	mov rdi, .fs_backslash
	mov rsi, rbx

.printf:
	push rax
	push rcx
	mov rax, 0
	call printf
	pop rcx
	pop rax

	dec rcx
	inc rax
	jmp .loop

.done:
	mov rax, 0
	mov rdi, .double_quote
	call printf

	pop rbp
	ret
section .data
.double_quote:
	db CHAR_DOUBLEQUOTE, 0
.fs_simple_char:
	db "%c", 0
.fs_hex_char:
	db "\x%02x;", 0	
.fs_tab:
	db "\t", 0
.fs_page:
	db "\f", 0
.fs_return:
	db "\r", 0
.fs_newline:
	db "\n", 0
.fs_doublequote:
	db CHAR_BACKSLASH, CHAR_DOUBLEQUOTE, 0
.fs_backslash:
	db CHAR_BACKSLASH, CHAR_BACKSLASH, 0

write_sob_pair:
	push rbp
	mov rbp, rsp

	push rsi
	
	mov rax, 0
	mov rdi, .open_paren
	call printf

	mov rsi, [rsp]

	CAR rsi, rsi
	call write_sob

	mov rsi, [rsp]
	CDR rsi, rsi
	call write_sob_pair_on_cdr
	
	add rsp, 1*8
	
	mov rdi, .close_paren
	mov rax, 0
	call printf

	pop rbp
	ret

section .data
.open_paren:
	db "(", 0
.close_paren:
	db ")", 0

write_sob_pair_on_cdr:
	push rbp
	mov rbp, rsp

	mov bl, byte [rsi]
	cmp bl, T_NIL
	je .done
	
	cmp bl, T_PAIR
	je .cdrIsPair
	
	push rsi
	
	mov rax, 0
	mov rdi, .dot
	call printf
	
	pop rsi

	call write_sob
	jmp .done

.cdrIsPair:
	CDR rbx, rsi
	push rbx
	CAR rsi, rsi
	push rsi
	
	mov rax, 0
	mov rdi, .space
	call printf
	
	pop rsi
	call write_sob

	pop rsi
	call write_sob_pair_on_cdr

.done:
	pop rbp
	ret

section .data
.space:
	db " ", 0
.dot:
	db " . ", 0

write_sob_symbol:
	push rbp
	mov rbp, rsp

	SYMBOL_VAL rsi, rsi
	
	STRING_LENGTH rcx, rsi
	STRING_ELEMENTS rax, rsi

	mov rdx, rcx

.loop:
	cmp rcx, 0
	je .done
	mov bl, byte [rax]
	and rbx, 0xff

	cmp rcx, rdx
	jne .ch_simple
	cmp rbx, '+'
	je .ch_hex
	cmp rbx, '-'
	je .ch_hex
	cmp rbx, 'A'
	jl .ch_hex

.ch_simple:
	mov rdi, .fs_simple_char
	mov rsi, rbx
	jmp .printf
	
.ch_hex:
	mov rdi, .fs_hex_char
	mov rsi, rbx

.printf:
	push rax
	push rcx
	mov rax, 0
	call printf
	pop rcx
	pop rax

	dec rcx
	inc rax
	jmp .loop

.done:
	pop rbp
	ret
	
section .data
.fs_simple_char:
	db "%c", 0
.fs_hex_char:
	db "\x%02x;", 0	

write_sob_closure:
	push rbp
	mov rbp, rsp

	CLOSURE_CODE rdx, rsi
	CLOSURE_ENV rsi, rsi

	mov rdi, .closure
	mov rax, 0
	call printf

	pop rbp
	ret
section .data
.closure:
	db "#<closure [env:%p, code:%p]>", 0

section .text
write_sob:
	mov rbx, 0
	mov bl, byte [rsi]	
	jmp qword [.jmp_table + rbx * 8]

section .data
.jmp_table:
	dq write_sob_undefined, write_sob_void, write_sob_nil
	dq write_sob_rational, write_sob_float, write_sob_bool
	dq write_sob_char, write_sob_string, write_sob_symbol
	dq write_sob_closure, write_sob_pair

section .text
write_sob_if_not_void:
	mov rsi, rax
	mov bl, byte [rsi]
	cmp bl, T_VOID
	je .continue

	call write_sob
	
	mov rax, 0
	mov rdi, .newline
	call printf
	
.continue:
	ret
section .data
.newline:
	db CHAR_NEWLINE, 0