if version < 600
  syntax clear
elseif exists("b:current_syntax")
  finish
endif

syn keyword     Statement       forall exists eval def

" capitalized words are types
syn match       Type "\<\u\w*\>"

" lowercase words are variables or methods
syn match       Function "\<\l\w*"

" C style integers ripped from c.vim
syn match       cNumbers        display transparent "\<\d\|\.\d" contains=cNumber
syn match       cNumber         display contained "\d\+\(u\=l\{0,2}\|ll\=u\)\>"
hi def link cNumber             Number

" C style strings ripped from c.vim
syn match       cSpecial    display contained "\\\(x\x\+\|\o\{1,3}\|.\|$\)"
syn region      String  start=+L\="+ skip=+\\\\\|\\"\|\\$+ excludenl end=+"+ end='$' contains=cSpecial,@Spell
hi def link cSpecial            SpecialChar

" Python style comment
syn match coolComment "#.*$" contains=coolTodo
hi def link coolComment         Comment

syn keyword  coolTodo contained TODO FIXME XXX
hi def link coolTodo            Todo
