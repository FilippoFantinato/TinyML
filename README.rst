TinyML
======

TinyML is an interpreter for a small functional language.
The grammar of the 

.. math::
    
    M ::= x \; | \; let \; [rec] \; x \; [:T] \; = \; M_1 \; in \; M_2 \; | \; M_1 \; bin\_op \; M_2 \; | \; un\_op M  \; | \; M_1 \; M_2 \; | \; fn \; (x \; [:T]) \; [:T] \to M

where 

.. math::
    
    T ::= float \; | \; int \; | \; char \; | \; string \; | \; bool \; | \; unit \; | \; T \to T \; | \; (T_1, T_2, \dots , T_n)

.. math::

    bin\_op ::= + \; | \; - \; | \; * \; | \; / \; | \; 
    \newline
    un\_op ::= - \; | \; not
