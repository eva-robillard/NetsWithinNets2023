// Code for the "Eval" class
// To compile all the required files, just execute "javac *.java"

import java.util.Set;
import java.util.Iterator;
import java.util.TreeMap;
import java.util.HashSet;
import java.util.HashMap;
import java.util.SortedMap;

public class Eval {
    // P-indexed: partition occupacy multiset
    private static String partitionOccStr;                  
    private static SMultiSet partitionOccBag;

    // P-indexed: partition capacity multiset; "4'p1,1'p2,1'p3,1'p4,1'p5"
    private static String capStr;                  
    private static SMultiSet capBag;

    // Y-indexed: "h" mapping. For a given p\in P, h(p) is the
    // set of regions to which p belongs
    // "p1,b4|p5,b1|...|p4,b1,b2"
    private static String hStr;                  
    private static SortedMap<String,Set<String>> hBag;

    // set B of boolean variables. They will be extracted from "hBag"
    private static Set<String> B;

    // set P of partitions. They will be extracted from "capBag"
    private static Set<String> P;

    static final String SEP = "'";

    //---------------------------------------------------------------------------
    // Initialization function with initial global capacity, region occupancy
    // and h function
     public Eval(String cap,String part,String h) {
        capStr = cap;
        partitionOccStr = part;

        capBag = new SMultiSet(cap);
        partitionOccBag = new SMultiSet(partitionOccStr);

        hStr = h;
        hBag = h2bag(hStr);

        // compute B set
        B = new HashSet<String>();
        for (SortedMap.Entry<String,Set<String>> entry : hBag.entrySet()) {
            B.addAll(entry.getValue());
        }

        // compute P set
        P = capBag.keySet();
    }
    //---------------------------------------------------------------------------
    //"hS" is of the form "p1,b4|p5,b1|p2,b3|p3,b2|p4,b1,b2"
    // returns a map such that res[p4]={b1,b2},res[p1]={b4},...
    public static SortedMap<String,Set<String>> h2bag(String hS) {

        SortedMap<String,Set<String>> res = new TreeMap<String,Set<String>>();
        String[] els = hS.split("\\|");

        for (String s : els) {
            String[] h_p = s.split(",");
            Set<String> images = new HashSet<String>();
            for (int i=1;i<h_p.length;i++) {
                images.add(h_p[i]);
            }
            res.put(h_p[0],images);
        }
       
        return res;
    }
    //---------------------------------------------------------------------------
    //"hB" is of the form hB[p4]={b1,b2},hB[p1]={b4},...
    // returns a string of the form "p1,b4|p5,b1|p2,b3|p3,b2|p4,b1,b2"
    public static String h2string(SortedMap<String,Set<String>> hB) {
        String res = "";

        for (SortedMap.Entry<String,Set<String>> entry : hB.entrySet()) {
            res = res + entry.getKey();
            for (String s : entry.getValue()) {
                res = res + "," + s;
            }
            res = res + "|";
        }

        if (res.endsWith("|")) {
            res = res.substring(0, res.length() - 1);
        }
       
        return res;
    }
    //---------------------------------------------------------------------------
    // Efficiency must be improved!!!!
    // Pre: f1="a,!b,c",f2="d,b,c",and neither f1 nor f2 have contradictions
    // Post: Can we find some "x" and "!x"?
    public static boolean isThereAContradiction(String f1,String f2) {
        String[] sF1 = f1.split(",");
        String[] sF2 = f2.split(",");
        for (String s1 : sF1) {
            for(String s2 : sF2) {
                // System.out.println(s1 + "-" + s2);
                if (s1.startsWith("!") && (s2.equals(s1.substring(1)))) {
                    return true;
                }
                if (s2.startsWith("!") && (s1.equals(s2.substring(1)))) {
                    return true;
                }
            }
        }
        return false;
    }

    // "FormPresAndPosts" is a number of triples of the form "String robotForm,String PreCap,String PostCap"
    public static boolean gef_many(String buchForm,String... FormPresAndPosts) {
        SMultiSet preMS = new SMultiSet();
        SMultiSet postMS = new SMultiSet();
        String robotForm = "";

        int nRobots = FormPresAndPosts.length / 3;

        int pos = 0;
        for (int r=0;r<nRobots;r++) {
            //[pos]: buchi formula; [pos+1]: pre multiset; [pos+2]: post multiset;

            // not necessary, since robot formulas HAVE NOT NEGATIONS in the new approach
            // if (isThereAContradiction(robotForm,FormPresAndPosts[pos])) {
            //     return false;
            // }
            robotForm = robotForm + "," + FormPresAndPosts[pos];
            preMS.add(new SMultiSet(FormPresAndPosts[pos+1]));
            postMS.add(new SMultiSet(FormPresAndPosts[pos+2]));
            pos += 3;
        }

        return gef_one(buchForm,robotForm,preMS,postMS);
    }

    // "buchForm" is of the form "b1,b2,!b3,!b4"
    // "robotForm" is of the form "b1,b5" (no negations): after execution, b1&b5
    // "capChange" is a P-multiset establishing the "partitionOcc" variation: neg components
    // represent cap resources engaged, positive values resources freed
    // Computes gef value for one robot transition
    public static boolean gef_one(String buchForm,String robotForm,SMultiSet preMS,SMultiSet postMS) {
        SMultiSet buchMS = new SMultiSet(buchForm);
        SMultiSet robotMS = new SMultiSet(robotForm);

        // capacity must be greaterOrEqual than the new necessities
        SMultiSet newPartitionOccBag = capBag.add(partitionOccBag,preMS);


        if (!capBag.greaterOrEqual(newPartitionOccBag)) {
            return false;
        }

        // Is buchForm true?
        if (buchForm == "1") {
            return true;
        }
        //since pre is verified, we must also add the freed resources
        newPartitionOccBag.add(postMS);

        // Last part of the algorithm, line 12 ...
        Set<String> tS = buchMS.keySet();
        
        for (String b : B) {
            int rOcc = ROIOccupancy(newPartitionOccBag,b);
            if (tS.contains(b) && (rOcc == 0)) {
                return false;
            }
            if (tS.contains("!"+b) && (rOcc >= 1)) {
                return false;
            }
        }
        
        return true;
    }

    public static boolean gef(String buchForm,String robForm1,String PreCap,String PostCap) {
        return gef_many(buchForm,robForm1,PreCap,PostCap);
    }

    public static boolean gef(String buchForm,
                              String robotForm1,String PreCap1,String PostCap1,
                              String robotForm2,String PreCap2,String PostCap2) {
        return gef_many(buchForm,robotForm1,PreCap1,PostCap1,robotForm2,PreCap2,PostCap2);
    }

    public static boolean gef(String buchForm,
                              String robotForm1,String PreCap1,String PostCap1,
                              String robotForm2,String PreCap2,String PostCap2,
                              String robotForm3,String PreCap3,String PostCap3) {
        return gef_many(buchForm,robotForm1,PreCap1,PostCap1,robotForm2,PreCap2,PostCap2,robotForm3,PreCap3,PostCap3);
    }
    //---------------------------------------------------------------------------
    // "PrePost" is a number of pairs of the form "preMS,postMS" 
    public static void updateCap_many(String... PrePost) {
        SMultiSet preMS = new SMultiSet();
        SMultiSet postMS = new SMultiSet();
        int nPairs = PrePost.length / 2;

        int pos = 0;
        for (int p=0;p<nPairs;p++) {
            //[pos]: pre multiset; [pos+1]: post multiset
            partitionOccBag.add(new SMultiSet(PrePost[pos])); //engaging new capacity
            partitionOccBag.diff(new SMultiSet(PrePost[pos+1])); //freeing capacity
            pos += 2;
        }
    }
    
    public static void updateCap(String pre1,String post1) {
        updateCap_many(pre1,post1);
    }

    public static void updateCap(String pre1,String post1,String pre2,String post2) {
        updateCap_many(pre1,post1,pre2,post2);
    }

    public static void updateCap(String pre1,String post1,String pre2,String post2,String pre3,String post3) {
        updateCap_many(pre1,post1,pre2,post2,pre3,post3);
    }
    //---------------------------------------------------------------------------
    // Given two solution paths, returns the "best" one. In this version,
    // "best" means less steps in the mission net (in a solution, steps are
    // in the string separated by means of '\n')
    public static String select_best(String oldV, String newV) {
        //Java8: counts the number of '\n' in a string
        long oldVc = oldV.chars().filter(nl -> nl == '\n').count();
        long newVc = newV.chars().filter(nl -> nl == '\n').count();
        if ((oldVc == 0) || (oldVc > newVc)) {//initial case or new is longer
           return newV;
        }
        else {
           return oldV;
        }
     } 
    //---------------------------------------------------------------------------
    // "b" is a ROI, "partitionOccBag" is an occupancy multiset
    // returns the marking of places p\in P such that b\in h(p)
    // TODO, not tested
    private static int ROIOccupancy(SMultiSet partitionOccBag,String b) {
        int res = 0;
        for (String key : partitionOccBag.keySet()) {

            if (hBag.get(key).contains(b)) {
                res = res + partitionOccBag.getVal(key);
            }
        }

        return res;
    }
    //---------------------------------------------------------------------------
    //For testing
    public static void main(String[] arg) {
        String cap = "1'p1,1'p2,1'p3,4'p4,1'p5";
        String partOcc = "3'p4";
        String h = "p1,b1|p2,b2,b3|p3,b2|p4,b4|p5,b3";
        Eval eval = new Eval(cap,partOcc,h);

        System.out.println("h:" + h2string(h2bag(h)));
        System.out.println("b4: " + ROIOccupancy(partitionOccBag,"b4"));
        System.out.println("b1: " + ROIOccupancy(partitionOccBag,"b1"));
        System.out.println("partitionOccBag:" + partitionOccBag.toString());

        // move from p1 to p5
        if(gef("b4","b1","1'p1","1'p4")) {
            System.out.println("OK");
            updateCap("1'p1","1'p4");
            System.out.println("new occ:" + partitionOccBag.toString());
        }
        else {
            System.out.println("A bad situation");
        }

        System.out.println(isThereAContradiction("a,b","a,c"));
        System.out.println(isThereAContradiction("a,b","c,!b"));
        
    }
}