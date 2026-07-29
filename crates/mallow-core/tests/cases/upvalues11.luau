local get, set
do
    local v = 100
    get = function() return v end
    set = function(x) v = x end
end

print(get())
set(67)
print(get())
