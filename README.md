impscript
=========

Gradual Types for JavaScript

Licenses
--------

1) TODO          : ImpScript
2) LICENSE.LamJS : LambdaJS by Arjun Guha and Claudiu Saftoiu (in src/LamJS)

Hello World Sample
------------------

% cd ~/impscript/src
% make
...
% ./impscript ../tests/simple-0/
% ./impscript ../tests/simple-0/negate.js 

DESUGARING: OK
Wrote to ../tests/simple-0/negate.is.

TC + CASTS: OK
Wrote to ../tests/simple-0/negate.1.is.

TC: OK
% ./impscript ../tests/simple-0/negate.1.is 

TC + CASTS: OK
Wrote to ../tests/simple-0/negate.2.is.

TC: OK
