/**
 * 
 **/
import java.util.HashMap;

public class TwoSum {
    public int[] twoSum(int[] nums, int target)
    {
        HashMap<Integer, Integer> map = new HashMap<Integer, Integer>();
        for (int i =0; i< nums.length; i++){
            int remainder = target - nums[i];
            if (map.containsKey(remainder)){
                return new int[]{(int)map.get(remainder), i};
            }
            map.put(nums[i], i);
        }
        return null;
    }
    
    public void printarray(int[] arr){
        System.out.print("[");
        for (int i =0; i< arr.length; i++){
            System.out.print(arr[i] + ", ");
        }
        System.out.println("]");
    }
    
    public static void main(String[] args)
    {
        int [] nums = new int[]{2, 16, 11, 15, 7, 9, 10};
        int tar1 = 9;
        int tar2 = 18;
        int tar3 = 25;
        TwoSum sm = new TwoSum();
        sm.printarray(sm.twoSum(nums, tar1));
        sm.printarray(sm.twoSum(nums, tar2));
        sm.printarray(sm.twoSum(nums, tar3));
    }
}
