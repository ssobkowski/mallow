-- a parameter captured by reference inside a loop at the very start of a function.
-- the loop header is the entry block, so the cell must be opened before it.
local fs = {}
local function fill(a)
    while #fs < 3 do
        fs[#fs + 1] = function()
            a = a + 1
            return a
        end
    end
    return a
end

print(fill(10))
print(fs[1](), fs[2](), fs[3]())
