local function consume(offset, size)
    while size > 0 do
        offset += 1
        size -= 1
    end

    return offset, size
end

local callback = select(1, consume) -- black box
print(callback(0, 2))
