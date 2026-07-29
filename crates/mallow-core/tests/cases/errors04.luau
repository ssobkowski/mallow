local function handler(msg)
    return "caught: " .. tostring(msg)
end

local ok, result = xpcall(function()
    error("raw")
end, handler)

print(not ok)
print(result:find("raw") ~= nil) -- if we printed result directly we would print the file path, which would fail the tests
