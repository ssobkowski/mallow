local bxor
for k, v in ipairs(_VERSION == "Lua 5.2" and { "bit32", "bit" } or { "bit", "bit32" }) do
    if type(_G[v]) == "table" and rawget(_G[v], "bxor") then
        bxor = _G[v].bxor
        break
    end
end
print(bxor and bxor(72, 38))
