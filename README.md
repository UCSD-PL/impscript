impscript
=========

Gradual Types for JavaScript

Licenses
--------

    1) TODO          : ImpScript
    2) LICENSE.LamJS : LambdaJS by Arjun Guha and Claudiu Saftoiu (in src/LamJS)

Execution Modes
---------------

    Usage: ./impscript [options] (file.js | file.is | file.n.is)

      Input       Mode
      ---------   -----------------------------------------------

      file.js     1) Desugar JavaScript to ImpScript file.0.is
                  2) Type check and insert casts in file.1.is
                  3) Type check file.1.is (sanity check)

      file.n.is   1) Type check and insert casts in file.n+1.is
                  2) Type check file.n+1.is (sanity check)

      file.is     1) Type check file.is


Sample Tests
------------

    % cd ~/impscript/src

    % make
    ...

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

    % ../scripts/run.py
    ...
