/*
 * https://leetcode.com/problems/clone-graph/description/
 * */
/**
 * Definition for undirected graph.
 * class UndirectedGraphNode {
 *     int label;
 *     List<UndirectedGraphNode> neighbors;
 *     UndirectedGraphNode(int x) { label = x; neighbors = new ArrayList<UndirectedGraphNode>(); }
 * };
 */
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;


public class CloneGraph {
    public UndirectedGraphNode cloneGraph(UndirectedGraphNode node) {
        if (node == null){
            return null;
        }
        HashMap<Integer,UndirectedGraphNode > created = new HashMap<Integer, UndirectedGraphNode>();
        HashSet<Integer> processed = new HashSet<Integer>();
        LinkedList<UndirectedGraphNode> queue = new  LinkedList<UndirectedGraphNode>();
        UndirectedGraphNode clone_root = new UndirectedGraphNode(node.label);
        created.put(node.label,clone_root);
        queue.add(node);
        while(!queue.isEmpty()){
            UndirectedGraphNode curr_n = queue.pop();
            Integer key = curr_n.label;
            //Check if current node is already processed
            if(processed.contains(key)){
                continue;
            }
            UndirectedGraphNode clone_n = null;
            if(created.containsKey(key)){
                clone_n = created.get(key);
            }else{
                clone_n = new UndirectedGraphNode(key);
                created.put(key, clone_n);
            }
            
            for(UndirectedGraphNode child : curr_n.neighbors){
                UndirectedGraphNode clone_child = null;
                if(created.containsKey(child.label)){
                    clone_child = created.get(child.label);
                }else{
                    clone_child = new UndirectedGraphNode(child.label);
                    created.put(child.label, clone_child);
                }
                clone_n.neighbors.add(clone_child);
                queue.add(child);
            }
            
            // this node has been processed and should not be considered again
            processed.add(key);
            
        }
        return clone_root;
    }
    
    class UndirectedGraphNode {
        int label;
        List<UndirectedGraphNode> neighbors;
        UndirectedGraphNode(int x) {
            label = x; 
            neighbors = new ArrayList<UndirectedGraphNode>(); 
        }
    };
}
