MODEL LAUNCHING PROCEDURE :

1) Open the Powershell in the directory containing the Java script Eval.java
2) Execute "javac Eval.java"
3) Open Renew from the Powershell (path of the directory containing the Renew software adding \renew ) 
4) Open "system_net.rnw" directly in Renew
5) Simulate Step by Step (Ctrl+I) or completely (Ctrl+R)


Some remarks : 
-At all times, you can observe the state of the robots nets by right-clicking the number contained by the Master Net place and double-clicking on one robot. 
-You can simulate by choosing the fired place. After having fired "init", you can double click on a transition si and choose what transition to fire. 
-This simulation is done for an LTL formula which implies the visit of three regions of interest ("a", "b", "c"), but requiring the visit of region "c" before visintg "a". The team of 3 robots evolves in an environment with 3 regions of interest from which two of them overlap.
