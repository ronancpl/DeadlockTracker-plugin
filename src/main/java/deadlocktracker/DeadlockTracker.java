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

import org.antlr.v4.runtime.tree.*;

import deadlocktracker.containers.DeadlockEntry;
import deadlocktracker.containers.DeadlockLock;
import deadlocktracker.containers.DeadlockStorage;
import deadlocktracker.source.JavaReader;
import deadlocktracker.source.CSharpReader;

import java.io.*;
import java.util.ArrayList;
import java.util.List;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Properties;
import java.util.Set;

/**
 *
 * @author RonanLana
 */
@Mojo(name = "execute")
public class DeadlockTracker extends AbstractMojo {

	private static boolean isSourceFile(String fName) {
		List<String> list = DeadlockConfig.getAssociatedFileExtensions();

		if (list.isEmpty()) {
			return true;
		}

		for (String ext : list) {
			if (fName.endsWith(ext)) {
				return true;
			}
		}

		return false;
	}

	private static void listSourceFiles(String directoryName, List<String> files) {
		File directory = new File(directoryName);

		// get all the files from a directory
		File[] fList = directory.listFiles();
		for (File file : fList) {
			if (file.isFile()) {
				String fName = file.getName();
				if(isSourceFile(fName)) {
					files.add(file.getAbsolutePath());
				}
			} else if (file.isDirectory()) {
				listSourceFiles(file.getAbsolutePath(), files);
			}
		}
	}

	private static DeadlockStorage parseSourceProject(String directoryName, DeadlockGraphMaker g, ParseTreeListener reader) {
		List<String> fileNames = new ArrayList<>();
		listSourceFiles(directoryName, fileNames);

		for(String fName : fileNames) {
			System.out.println("Parsing '" + fName + "'");
			g.parseSourceFile(fName, reader);
		}
		System.out.println("Project file reading complete!\n");

		DeadlockStorage ret;
		if (reader instanceof JavaReader) {
			ret = ((JavaReader) reader).compileProjectData();
		} else if (reader instanceof CSharpReader) {
			ret = ((CSharpReader) reader).compileProjectData();
		} else {
			ret = null;
		}

		return ret;     // finally, updates the storage table with relevant associations
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
		ParseTreeListener l = DeadlockConfig.getSourceParserFromProperty(("language"));

		String directoryName = DeadlockConfig.getProperty("src_folder");
		if (l instanceof CSharpReader) ((CSharpReader) l).setSourceDirPrefixPath(directoryName);

		DeadlockStorage md = parseSourceProject(directoryName, g, l);
		System.out.println("Project parse complete!\n");

		DeadlockGraph mdg = g.generateSourceGraph(md);
		System.out.println("Project graph generated!\n");

		Map<Integer, String> r = getGraphLockNames(g);
		Set<DeadlockEntry> mds = new DeadlockGraphCruiser().runSourceGraph(mdg, md, r);
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
