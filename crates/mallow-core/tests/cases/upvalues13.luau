-- a local captured by reference on only one branch of an if/else.
-- the uncaptured branch's writes must survive the join.
local function pick(flag)
    local a, b
    if flag then
        a, b = "direct", "value"
    else
        b = function()
            return a
        end
        a = "captured"
    end
    return a, b
end

print(pick(true))
local _, read = pick(false)
print(read())
