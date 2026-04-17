local Animal = {}
Animal.__index = Animal

function Animal.new(name, sound)
    return setmetatable({ name = name, sound = sound }, Animal)
end

function Animal:speak()
    return self.name .. " says " .. self.sound
end

local cat = Animal.new("cat", "meow")
print(cat:speak())
