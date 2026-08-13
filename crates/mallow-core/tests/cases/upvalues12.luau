local function pair()
    return "first", "second"
end

local function assign_pair()
    local captured = "before"
    local function read()
        return captured
    end

    local other
    captured, other = pair()
    return read(), other
end

print(assign_pair())
