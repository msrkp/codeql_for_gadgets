import javascript
import semmle.javascript.security.dataflow.DOM

/*
$( "#" + $.escapeSelector(window.location.hash.substr(1)) + "" ).trigger( 'click' );
*/

 class Source extends DataFlow::Node  {
    Source() { this = DOM::locationSource() }
  }

/*
from DataFlow::SourceNode n, DataFlow::CallNode call, JQuery::MethodCall mc
where
  n = jquery() and
  call = n.getACall() and 
  mc = call.getAChainedMethodCall("trigger") and
mc.getArgument(0).toString().matches("%click%")
select call.getArgument(0), mc.getArgument(0).toString()
*/
 class Configuration extends TaintTracking::Configuration {
   
   Configuration() { this = "gadgets1" }
   
   override predicate isSource(DataFlow::Node source) { 
       source instanceof Source 
   }
   
   override predicate isSink(DataFlow::Node sink) {
     exists( DataFlow::SourceNode n, DataFlow::CallNode call, JQuery::MethodCall mc |
       n = jquery() and
       call = n.getACall() and
       mc = call.getAChainedMethodCall("trigger") and
       mc.getArgument(0).toString().matches("%click%") and	
		sink = call.getArgument(0)

     )
   }
}

from Configuration cfg, DataFlow::PathNode source, DataFlow::PathNode sink
where cfg.hasFlowPath(source, sink)
select sink.getNode(), source, sink, "Found a gadget"
   
