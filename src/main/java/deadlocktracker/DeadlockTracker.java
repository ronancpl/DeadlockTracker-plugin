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

import org.apache.maven.plugin.AbstractMojo;
import org.apache.maven.plugin.MojoExecutionException;
import org.apache.maven.plugins.annotations.Mojo;

import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.tree.*;

import deadlocktracker.containers.DeadlockEntry;
import deadlocktracker.containers.DeadlockLock;
import deadlocktracker.containers.DeadlockStorage;
import deadlocktracker.source.JavaReader;
import deadlocktracker.graph.maker.JavaGraph;

import java.io.*;
import java.util.ArrayList;
import java.util.List;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Properties;
import java.util.Set;

import language.java.*;

/**
 *
 * @author RonanLana
 */
@Mojo(name = "execute")
public class DeadlockTracker extends AbstractMojo {

    private static void parseJavaFile(String fileName, JavaReader listener) {
        try {
            JavaLexer lexer = new JavaLexer(CharStreams.fromFileName(fileName));
            CommonTokenStream commonTokenStream = new CommonTokenStream(lexer);
            JavaParser parser = new JavaParser(commonTokenStream);
            ParseTree tree = parser.compilationUnit();
            
            ParseTreeWalker walker = new ParseTreeWalker();
            walker.walk(listener, tree);
        } catch (IOException e) {
            e.printStackTrace();
        }
    }
    
    private static void listJavaFiles(String directoryName, List<String> files) {
        File directory = new File(directoryName);

        // get all the files from a directory
        File[] fList = directory.listFiles();
        for (File file : fList) {
            if (file.isFile()) {
                String fName = file.getName();
                if(fName.endsWith(".java")) {
                    files.add(file.getAbsolutePath());
                }
            } else if (file.isDirectory()) {
                listJavaFiles(file.getAbsolutePath(), files);
            }
        }
    }
    
    private static DeadlockStorage parseJavaProject(String directoryName) {
        List<String> fileNames = new ArrayList<>();
        listJavaFiles(directoryName, fileNames);
        
        JavaReader reader = new JavaReader();
        
        for(String fName : fileNames) {
            System.out.println("Parsing '" + fName + "'");
            parseJavaFile(fName, reader);
        }
        System.out.println("Project file reading complete!\n");
        
        return JavaReader.compileProjectData();     // finally, updates the storage table with relevant associations
    }
    
    private static void loadPropertiesFile() {
        Properties prop = new Properties();
        String fileName = "config.cfg";
        try (FileInputStream fis = new FileInputStream(fileName)) {
            prop.load(fis);
        } catch (IOException ex) {
            ex.printStackTrace();
        }
        
        DeadlockConfig.loadProperties(prop);
    }
    
    private static Map<Integer, String> getGraphLockNames(DeadlockGraphMaker g) {
        Map<Integer, String> r = new HashMap<>();
        
        Map<String, DeadlockLock> m = g.getGraphLocks();
        for (Entry<String, DeadlockLock> em : m.entrySet()) {
            if(em.getValue() != null) r.put(em.getValue().getId(), em.getKey());
        }
        
        return r;
    }
    
    private static void executeDeadlockTracker() {
        loadPropertiesFile();
        
        DeadlockGraphMaker g = DeadlockConfig.getGraphMakerFromProperty(("language"));
        
        DeadlockStorage md = parseJavaProject(DeadlockConfig.getProperty("src_folder"));
        System.out.println("Project parse complete!\n");
        
        DeadlockGraph mdg = g.generateSourceGraph(md);
        System.out.println("Project graph generated!\n");
        
        Map<Integer, String> r = getGraphLockNames(g);
        Set<DeadlockEntry> mds = new DeadlockGraphCruiser().runSourceGraph(mdg, r);
        DeadlockGraphResult.reportDeadlocks(mds, r);
        
        //DeadlockGraphMaker.dumpGraph();
        
    }
    
    @Override
    public void execute() throws MojoExecutionException {
        executeDeadlockTracker();
    }
    
    public static void main(String[] args) {
        executeDeadlockTracker();
    }
}
