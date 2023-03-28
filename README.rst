TinyML
======

TinyML is an interpreter for executing programs written in a small functional language.
The grammar 

.. math::
    
    M ::= x \; | \; let \; [rec] \; x \; [: \; T] \; = \; M \; in \; M \; | \; M_1 \; op \; M_2 \; | \; M_1 \; M_2 \; | \; fn \; x \to M
