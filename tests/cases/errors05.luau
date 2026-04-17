local function level2()
    error("deep", 2) -- blame the caller
end

local ok, msg = pcall(level2)
print(not ok)
print(typeof(msg) == "string")
