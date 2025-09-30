/*
    This file is part of the DeadlockTracker detection tool
    Copyleft (L) 2025 RonanLana

    GNU General Public License v3.0

    Permissions of this strong copyleft license are conditioned on making available complete
    source code of licensed works and modifications, which include larger works using a licensed
    work, under the same license. Copyright and license notices must be preserved. Contributors
    provide an express grant of patent rights.
*/
package deadlocktracker;

import java.util.ArrayList;
import java.util.List;
import java.util.Properties;

import deadlocktracker.graph.maker.CSharpGraph;
import deadlocktracker.graph.maker.JavaGraph;

/**
 *
 * @author RonanLana
 */
public class DeadlockConfig {
    
	private enum Language {

		JAVA("java", JavaGraph.class),
		CSHARP("c#", CSharpGraph.class),
		UNSUPPORTED("", null);
		
		private final String name;
		private final Class<? extends DeadlockGraphMaker> class_;
		
		private Language(String name, Class<? extends DeadlockGraphMaker> class_) {
			this.name = name;
			this.class_ = class_;
		}
		
		private String getName() {
			return this.name;
		}
		
		private Class<? extends DeadlockGraphMaker> getClass_() {
			return this.class_;
		}
		
		public static Class<? extends DeadlockGraphMaker> getGraphMakerByName(String name) {
			name = name.trim().toLowerCase();
			for (Language l : Language.values()) {
				if(l.getName().contentEquals(name)) {
					return l.getClass_();
				}
			}
			
			return UNSUPPORTED.getClass_();
		}
		
	}
	
    private static Properties prop;
    private static List<String> extensions;
        
    public static String getProperty(String key) {
        return prop.getProperty(key);
    }
    
    public static void loadProperties(Properties properties) {
        prop = properties;
        loadAssociatedFileExtensions();
    }
    
    public static void loadAssociatedFileExtensions() {
    	extensions = new ArrayList<>();
    	for (String sp : getProperty("extensions").split(",")) {
    		sp = sp.trim();
    		if (!sp.isEmpty()) {
    			extensions.add("." + sp);    			
    		}
    	}
    }
    
    public static DeadlockGraphMaker getGraphMakerFromProperty(String key) {
    	try {
    		return Language.getGraphMakerByName(getProperty(key).trim()).newInstance();
    	} catch (IllegalAccessException | InstantiationException | NullPointerException e) {
    		e.printStackTrace();
    		return null;
    	}
    }
    
    public static List<String> getAssociatedFileExtensions() {
    	return extensions;
    }
}
