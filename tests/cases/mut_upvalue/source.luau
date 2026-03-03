local mut_upvalue = 0
local function captures_upvalue()
  mut_upvalue += 50
end

for i = 1, 10 do
  local old = mut_upvalue
  captures_upvalue()
  print(old, mut_upvalue)
end
