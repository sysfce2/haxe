package cases;

class Issue5141 extends DisplayTestCase {
	/**
		typedef MyHandler = Int->String->Void

		class Some {
			function main() {
				var a:MyHandler;
				a{-1-};
				a({-2-}
			}
		}
	**/
	function testTypedef() {
		eq("MyHandler", type(pos(1)));
		sigEq(0, [[":Int", ":String"]], signature(pos(2)));
	}

	/**
		@:callable
		abstract MyCallable(Int->String->Void) {}

		class Some {
			function main() {
				var a:MyCallable;
				a{-1-};
				a({-2-}
			}
		}
	**/
	function testAbstract() {
		eq("MyCallable", type(pos(1)));
		sigEq(0, [[":Int", ":String"]], signature(pos(2)));
	}
}
