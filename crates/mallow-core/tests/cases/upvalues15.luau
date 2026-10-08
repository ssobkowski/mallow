-- a local captured by reference on both branches of an if/else.
-- both closures must share one cell after the join.
local function pick(flag)
    local a = 0
    local get, set
    if flag then
        get = function()
            return a
        end
    else
        set = function(x)
            a = x
        end
    end
    a = a + 1
    return a, get, set
end

local a, get = pick(true)
print(a, get())
local b, _, set = pick(false)
set(5)
print(b)
