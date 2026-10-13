-- Compound conditions as `while` guards. Every iteration reads the next row
-- of inputs, so each guard sees changing values until it fails.
local rows = {
    { true, true, false, false },
    { false, false, true, true },
    { true, false, true, false },
    { false, true, false, true },
    { true, true, true, true },
    { false, false, false, false },
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
        local row = rows[i] or {}
        a, b, c, d = row[1], row[2], row[3], row[4]
    end

    i = start - 1
    load()
    while a and b or c do table.insert(out, "1") load() end
    i = start - 1
    load()
    while (a or b) and c do table.insert(out, "2") load() end
    i = start - 1
    load()
    while a and (b or c) do table.insert(out, "3") load() end
    i = start - 1
    load()
    while a and b or c and d do table.insert(out, "4") load() end

    log = {}
    i = start - 1
    load()
    while probe("a", a) and probe("b", b) or probe("c", c) do
        table.insert(log, "|")
        load()
    end

    return table.concat(out), table.concat(log)
end

for start = 1, #rows do
    print(start, run(start))
end
