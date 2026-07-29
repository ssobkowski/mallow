local state

local function write()
    state = {}
    state.value = 1
end

local function read()
    return state.value
end

write()
print(read())
