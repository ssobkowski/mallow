local ok, err = pcall(function()
    error("boom")
end)

print(not ok)
print(typeof(err))
