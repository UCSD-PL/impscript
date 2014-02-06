var f, g;
f = function () /*: {*g} => () -> (any) */ { g(); };
g = function () /*: {*f} => () -> (any) */ { f(); };
f();
