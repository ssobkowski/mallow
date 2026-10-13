-- Compound conditions in `if` statements, over every combination of inputs.
local log = {}

local function probe(name, value)
    table.insert(log, name)
    return value
end
probe = select(1, probe) -- black box

local function plain(a, b, c, d)
    local out = {}
    if a and b or c then table.insert(out, "1") else table.insert(out, "-") end
    if (a or b) and c then table.insert(out, "2") else table.insert(out, "-") end
    if a and (b or c) then table.insert(out, "3") else table.insert(out, "-") end
    if a and b or c and d then table.insert(out, "4") else table.insert(out, "-") end
    if not (a and b) or c then table.insert(out, "5") end
    if (a or b) and (c or d) then table.insert(out, "6") end
    return table.concat(out)
end

local function probed(a, b, c, d)
    log = {}
    if probe("a", a) and probe("b", b) or probe("c", c) then table.insert(log, "1") end
    if (probe("a", a) or probe("b", b)) and probe("c", c) then table.insert(log, "2") end
    if probe("a", a) and (probe("b", b) or probe("c", c)) then table.insert(log, "3") end
    if probe("a", a) and probe("b", b) or probe("c", c) and probe("d", d) then
        table.insert(log, "4")
    else
        table.insert(log, "!4")
    end
    return table.concat(log)
end

for mask = 0, 15 do
    local a = mask % 2 >= 1
    local b = mask % 4 >= 2
    local c = mask % 8 >= 4
    local d = mask >= 8
    print(mask, plain(a, b, c, d), probed(a, b, c, d))
end
