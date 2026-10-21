local g = select(1, function(x) return x end)
local x, y = 0, 0
while (g(x < 5) and g(y < 3)) or g(x == 7) do
  x += 1
  if g(x % 2 == 0) then y += 1 end
end
print(x, y)
