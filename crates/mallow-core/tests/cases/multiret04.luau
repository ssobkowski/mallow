local function out(...)
    local n = select("#", ...)
    local parts = {}
    for i = 1, n do
        local v = select(i, ...)
        parts[i] = tostring(v)
    end
    print(table.concat(parts, "|"))
end

local function many(tag)
    out("many", tag)
    return `{tag}:a`, `{tag}:b`, `{tag}:c`
end


local function fixed_from_call()
    local a, b = many("x")
    return a, b
end

local r1, r2, r3 = fixed_from_call()
out("result", r1, r2, r3)

local function fixed_with_nil()
    return "a", "b", nil, "d"
end

local function passthrough()
    return fixed_with_nil()
end

out("count", select("#", passthrough()))
out("values", passthrough())

local function fixed()
    return 10, 20, 30
end

local function f()
    local a, b = fixed()
    local c = a + b
    if c > 0 then
        c += 1
    end
    return a, b, c
end

out(f())

local start_value = 2
local end_value = 8
local step_value = 3

local sum = 0
local seen = ""

for i = start_value, end_value, step_value do
    sum += i
    seen = `{seen}{i},`
end

out("bounds", start_value, end_value, step_value)
out("loop", seen, sum)

local before = 100
local after = 0

for i = 1, 3 do
    if i == 1 then
        before += i
    end
    after = after * 10 + i
end

out(before, after)

local function iter(state, index)
    index = index + 1

    if index == 1 then
        return index, "a", 10
    elseif index == 2 then
        return index, "b", 20
    elseif index == 3 then
        return index, "c", 30
    end

    return nil
end

local keys = ""
local total = 0

for k, name, value in iter, nil, 0 do
    keys ..= `{k}:{name},`
    total += value
end

out(keys, total)

local function iter2(state, index)
    index = index + 1
    if index > #state then
        return nil
    end
    return index, state[index], index * 2
end

local data = { "x", "y", "z" }
local acc = ""

for i, item, doubled in iter2, data, 0 do
    acc ..= `{i}:{item}{doubled};`
end

out(acc)

local function f2(x)
    local y = x + 1

    if y == 4 then
        return "then", y
    else
        return "else", y
    end
end

out(f2(3))
out(f2(10))
