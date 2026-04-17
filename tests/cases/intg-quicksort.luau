local quick = {}

function quick.sort(array)
	local function partition(low, high)
		local pivot = array[high]
		local i = low - 1

		for j = low, high - 1 do
			if array[j] <= pivot then
				i += 1
				array[i], array[j] = array[j], array[i]
			end
		end

		array[i + 1], array[high] = array[high], array[i + 1]

		return i + 1
	end

	local function sort(low, high)
		if low < high then
			local pivot = partition(low, high)
			sort(low, pivot - 1)
			sort(pivot + 1, high)
		end

		return array
	end

	return sort(1, #array)
end

local nums = {775, 230, 288, 359, 969, 119, 812, 123, 970, 892, 165, 490, 438, 569, 502, 435, 747, 546, 191, 308, 867, 495, 670, 237, 407, 167, 223, 811, 428, 935, 182, 113, 197, 845, 180, 194, 466, 303, 838, 216, 517, 977, 413, 898, 694, 805, 975, 141, 410, 967, 868, 347, 902, 473, 472, 732, 129, 905, 814, 385, 205, 285, 630, 949, 770, 384, 363, 357, 728, 879, 736, 864, 752, 797, 663, 146, 757, 503, 784, 773, 699, 150, 836, 293, 248, 233, 168, 835, 351, 577, 982, 837, 598, 722, 464, 963, 262, 638, 582, 376}
print(table.concat(nums, ","))

quick.sort(nums)
print(table.concat(nums, ","))
