local function a()
    local x = 1
    return function()
        local y = x + 1
        return function()
            local z = y + 1
            return function()
                return x + y + z
            end
        end
    end
end

local result = a()()()()
print(result) -- x=1, y=2, z=3
