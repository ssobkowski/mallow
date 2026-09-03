local function forward_values(...)
    return ...
end

local forwarded_string, forwarded_number = forward_values("value", 42)
