local AND_OF_TWO_NIBBLES = {}

for idx = 0, 255 do
    local x = idx % 16
    local y = (idx - x) / 16
    local res = 0
    local w = 1
    while x * y ~= 0 do
        local rx = x % 2
        local ry = y % 2
        res += rx * ry * w
        x = (x - rx) / 2
        y = (y - ry) / 2
        w = w * 2
    end
    AND_OF_TWO_NIBBLES[idx] = res
end

local function and_or_xor(x, y, operation)
    local x0 = x % 65536
    local y0 = y % 65536
    local rx = x0 % 16
    local ry = y0 % 16
    local res = AND_OF_TWO_NIBBLES[rx + ry * 16]

    do
        local AND_OF_TWO_NIBBLES = false
        if AND_OF_TWO_NIBBLES then
            print("never")
        end
    end

    x = (x0 - rx) / 16
    y = (y0 - ry) / 16
    rx = x % 256
    ry = y % 16
    res += AND_OF_TWO_NIBBLES[rx + ry * 16] * 16

    if operation then
        res = x0 + y0 - operation * res
    end

    return res
end

print(and_or_xor(12345, 54321))
print(and_or_xor(12345, 54321, 1))
print(and_or_xor(12345, 54321, 2))
print(and_or_xor(65535, 0, 2))
