local function out(...)
    print(select("#", ...), ...)
end

local function pair()
    return "a", "b"
end

out("open call", pair())
out("fixed call", (pair()))
out("fixed prefix", pair(), "tail")

local a, b, c = "head", pair()
out("open assignment", a, b, c)

local d, e = pair(), "tail"
out("fixed assignment", d, e)

local function open_return()
    return "head", pair()
end

local function fixed_return()
    return pair(), "tail"
end

local function first_vararg(...)
    return (...)
end

out("open return", open_return())
out("fixed return", fixed_return())
out("fixed vararg", first_vararg(1, 2, 3))

local open_table = { "head", pair() }
local fixed_table = { (pair()) }
out("open table", #open_table, table.unpack(open_table))
out("fixed table", #fixed_table, table.unpack(fixed_table))

local function iterator(state, index)
    index += 1
    if index <= state then
        return index
    end
    return nil
end

local function make_iterator()
    return iterator, 2, 0
end

local seen = ""
for value in make_iterator() do
    seen ..= value
end
out("open generic for", seen)
