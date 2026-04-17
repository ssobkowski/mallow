local funcs = {}
for i = 1, 3 do
    local j = i
    funcs[i] = function() return j end
end

assert(funcs[1]() == 1)
assert(funcs[2]() == 2)
assert(funcs[3]() == 3)
