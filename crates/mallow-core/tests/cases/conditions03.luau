-- Compound conditions as `repeat` conditions. Every iteration reads the next
-- row of inputs, so each condition sees changing values until it holds.
local rows = {
    { false, true, false, false },
    { true, false, false, true },
    { false, false, true, false },
    { true, true, false, false },
    { false, true, true, true },
    { true, true, true, true },
}

local log = {}

local function probe(name, value)
    table.insert(log, name)
    return value
end
probe = select(1, probe) -- black box

local function run(start)
    local out = {}
    local i, a, b, c, d

    local function load()
        i += 1
        local row = rows[i] or { true, true, true, true }
        a, b, c, d = row[1], row[2], row[3], row[4]
    end

    i = start - 1
    repeat table.insert(out, "1") load() until a and b or c
    i = start - 1
    repeat table.insert(out, "2") load() until (a or b) and c
    i = start - 1
    repeat table.insert(out, "3") load() until a and (b or c)
    i = start - 1
    repeat table.insert(out, "4") load() until a and b or c and d

    log = {}
    i = start - 1
    repeat
        table.insert(log, "|")
        load()
    until (probe("a", a) or probe("b", b)) and probe("c", c)

    return table.concat(out), table.concat(log)
end

for start = 1, #rows do
    print(start, run(start))
end
