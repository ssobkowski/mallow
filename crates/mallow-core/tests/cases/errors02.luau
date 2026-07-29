local outer_ok = pcall(function()
    local inner_ok, _ = pcall(function()
        error("inner")
    end)
    print(not inner_ok)
end)

print(outer_ok)
