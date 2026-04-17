local call_count = 0

local function key()
    call_count = call_count + 1
    return "x"
end

local t = {}
t.x = 10

-- compound assignment: key() should only be called once
call_count = 0
t[key()] += 5
print(call_count)

-- manual expansion: key() gets called twice
call_count = 0
t[key()] = t[key()] + 5
print(call_count)
