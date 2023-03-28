TinyML
======

.. image:: https://github.com/FilippoFantinato/TinyML/actions/workflows/build-develop.yml/badge.svg?branch=develop
   :target: https://github.com/FilippoFantinato/TinyML/actions/workflows/build-develop.yml
   
.. image:: https://github.com/FilippoFantinato/TinyML/actions/workflows/build-main.yml/badge.svg?branch=main
   :target: https://github.com/FilippoFantinato/TinyML/actions/workflows/build-main.yml
   
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
