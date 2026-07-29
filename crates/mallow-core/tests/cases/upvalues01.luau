local value = 0

local function bump()
    value += 50
end

for _ = 1, 4 do
    local old = value
    bump()
    print(old, value)
end
