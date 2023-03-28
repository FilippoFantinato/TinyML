TinyML
======

TinyML is an interpreter for a small functional language with type inference.
I'm using this project for experiencing in type systems and crafting programming languages.

..  
    The grammar of the programming language is the following:
    
    .. math::

        M ::= x 
            | let [rec] x [:T] = M_1 in M_2 
            | M_1 bin_op M_2 
            | un_op M   
            | fn (x [:T]) [:T] -> M
            | M_1 M_2

    where 

    .. math::

        T ::= float | int | char | string | bool | unit | T -> T | (T_1, T_2,..., T_n)

        bin_op ::= + | - | * | / | % | < | <= | > | >= | = | <> 
        un_op ::= - | not
