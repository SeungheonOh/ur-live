'use client';

import { useEffect, useRef, useState } from 'react';
import {
  ArrowDown,
  ArrowUp,
  FileCode2,
  FilePlus2,
  PanelLeftClose,
  PanelLeftOpen,
  Pencil,
  Trash2,
  Upload,
} from 'lucide-react';
import { Button } from '@/components/ui/button';
import { Input } from '@/components/ui/input';
import {
  Collapsible,
  CollapsibleContent,
  CollapsibleTrigger,
} from '@/components/ui/collapsible';
import {
  NativeSelect,
  NativeSelectOption,
} from '@/components/ui/native-select';
import {
  Dialog,
  DialogContent,
  DialogDescription,
  DialogFooter,
  DialogHeader,
  DialogTitle,
} from '@/components/ui/dialog';
import {
  AlertDialog,
  AlertDialogAction,
  AlertDialogCancel,
  AlertDialogContent,
  AlertDialogDescription,
  AlertDialogFooter,
  AlertDialogHeader,
  AlertDialogTitle,
} from '@/components/ui/alert-dialog';
import { SourceEditor } from '@/components/code-surface';
import {
  validateFilename,
  validateProject,
  type BrowserProject,
} from '../public/project.mjs';

export function ProjectEditor({
  project,
  disabled,
  filesOpen,
  onFilesOpenChange,
  onChange,
  onCompile,
}: {
  project: BrowserProject;
  disabled: boolean;
  filesOpen: boolean;
  onFilesOpenChange: (open: boolean) => void;
  onChange: (project: BrowserProject) => void;
  onCompile: () => void;
}) {
  const [active, setActive] = useState(project.entry);
  const [dialog, setDialog] = useState<'new' | 'rename' | null>(null);
  const [filename, setFilename] = useState('');
  const [error, setError] = useState('');
  const [deleting, setDeleting] = useState(false);
  const [importing, setImporting] = useState(false);
  const input = useRef<HTMLInputElement>(null);
  const latest = useRef({ project, disabled });
  const mounted = useRef(true);
  useEffect(() => {
    latest.current = { project, disabled };
  }, [project, disabled]);
  useEffect(() => {
    mounted.current = true;
    return () => {
      mounted.current = false;
    };
  }, []);
  const locked = disabled || importing;
  const paths = project.order.flatMap((path) =>
    Object.hasOwn(project.files, path + 's') ? [path, path + 's'] : [path],
  );
  const implementation = active.endsWith('.urs') ? active.slice(0, -1) : active;
  const position = project.order.indexOf(implementation);

  const accept = (next: BrowserProject, nextActive = active) => {
    validateProject(next);
    onChange(next);
    setActive(nextActive);
    setError('');
  };
  const saveFilename = () => {
    try {
      const name = filename.trim();
      validateFilename(name);
      if (Object.hasOwn(project.files, name))
        throw new Error(`${name} already exists.`);
      const files = { ...project.files };
      let order = [...project.order];
      let entry = project.entry;
      if (dialog === 'rename') {
        if (name.endsWith('.urs') !== active.endsWith('.urs'))
          throw new Error('Keep the existing .ur or .urs extension.');
        files[name] = files[active];
        delete files[active];
        if (active.endsWith('.ur') && Object.hasOwn(files, active + 's')) {
          if (Object.hasOwn(files, name + 's'))
            throw new Error(`${name}s already exists.`);
          files[name + 's'] = files[active + 's'];
          delete files[active + 's'];
        }
        order = order.map((path) => (path === active ? name : path));
        if (entry === active) entry = name;
      } else {
        files[name] = '';
        if (name.endsWith('.ur'))
          order.splice(Math.max(0, order.indexOf(entry)), 0, name);
      }
      accept({ files, entry, order }, name);
      setDialog(null);
    } catch (problem) {
      setError(String(problem instanceof Error ? problem.message : problem));
    }
  };
  const move = (delta: number) => {
    const order = [...project.order];
    [order[position], order[position + delta]] = [
      order[position + delta],
      order[position],
    ];
    accept({ ...project, order });
  };

  return (
    <Collapsible
      className="project-editor"
      open={filesOpen}
      onOpenChange={onFilesOpenChange}
    >
      <header className="pane-toolbar source-toolbar">
        <CollapsibleTrigger
          render={<Button variant="ghost" size="sm" className="files-toggle" />}
          aria-label={filesOpen ? 'Hide files' : 'Show files'}
          title={filesOpen ? 'Hide files' : 'Show files'}
        >
          {filesOpen ? (
            <PanelLeftClose aria-hidden="true" />
          ) : (
            <PanelLeftOpen aria-hidden="true" />
          )}
          Files
        </CollapsibleTrigger>
        <span className="pane-title">
          <FileCode2 aria-hidden="true" />
          <label htmlFor={`source-${active}`}>{active}</label>
        </span>
      </header>
      <div className="project-body">
        <CollapsibleContent
          render={<aside />}
          className="project-files"
          aria-label="Project files in compilation order"
          keepMounted
        >
          <div className="file-toolbar">
            <span>Files</span>
            <Button
              variant="ghost"
              size="icon-sm"
              disabled={locked}
              title="New file"
              aria-label="New file"
              onClick={() => {
                setError('');
                setFilename('');
                setDialog('new');
              }}
            >
              <FilePlus2 />
            </Button>
            <Button
              variant="ghost"
              size="icon-sm"
              disabled={locked}
              title="Import .ur and .urs files"
              aria-label="Import files"
              onClick={() => input.current?.click()}
            >
              <Upload />
            </Button>
            <input
              ref={input}
              type="file"
              multiple
              accept=".ur,.urs"
              hidden
              onChange={async (event) => {
                const selectedFiles = Array.from(
                  event.currentTarget.files ?? [],
                );
                event.currentTarget.value = '';
                if (!selectedFiles.length) return;
                setImporting(true);
                try {
                  if (
                    selectedFiles.length + Object.keys(project.files).length >
                    64
                  )
                    throw new Error('A project can contain at most 64 files.');
                  if (
                    selectedFiles.reduce((n, file) => n + file.size, 0) >
                    256 * 1024
                  )
                    throw new Error('Import is larger than 256 KiB.');
                  const files = { ...project.files };
                  const order = [...project.order];
                  for (const file of selectedFiles) {
                    validateFilename(file.name);
                    if (Object.hasOwn(files, file.name))
                      throw new Error(
                        `${file.name} already exists; rename it before importing.`,
                      );
                    files[file.name] = await file.text();
                    if (file.name.endsWith('.ur'))
                      order.splice(order.indexOf(project.entry), 0, file.name);
                  }
                  if (!mounted.current) return;
                  if (
                    latest.current.project !== project ||
                    latest.current.disabled
                  )
                    throw new Error(
                      'The project changed or compilation started while importing. Please import again.',
                    );
                  accept({ ...project, files, order }, selectedFiles[0].name);
                } catch (problem) {
                  if (mounted.current)
                    setError(
                      String(
                        problem instanceof Error ? problem.message : problem,
                      ),
                    );
                } finally {
                  if (mounted.current) setImporting(false);
                }
              }}
            />
          </div>
          <ol className="file-list">
            {paths.map((path) => (
              <li key={path}>
                <button
                  type="button"
                  className="file-tab"
                  aria-current={active === path ? 'true' : undefined}
                  onClick={() => setActive(path)}
                  title={path}
                >
                  <span className="file-order">
                    {path.endsWith('.urs')
                      ? '·'
                      : project.order.indexOf(path) + 1}
                  </span>
                  <span className="file-name">{path}</span>
                  {path === project.entry && (
                    <span className="entry-mark" aria-label="Entry module">
                      main
                    </span>
                  )}
                </button>
              </li>
            ))}
          </ol>
          <div className="file-actions">
            <Button
              variant="ghost"
              size="icon-sm"
              disabled={locked || position === 0}
              title="Compile this module earlier"
              aria-label="Move module earlier"
              onClick={() => move(-1)}
            >
              <ArrowUp />
            </Button>
            <Button
              variant="ghost"
              size="icon-sm"
              disabled={locked || position === project.order.length - 1}
              title="Compile this module later"
              aria-label="Move module later"
              onClick={() => move(1)}
            >
              <ArrowDown />
            </Button>
            <Button
              variant="ghost"
              size="icon-sm"
              disabled={locked}
              title="Rename file"
              aria-label="Rename file"
              onClick={() => {
                setError('');
                setFilename(active);
                setDialog('rename');
              }}
            >
              <Pencil />
            </Button>
            <Button
              variant="ghost"
              size="icon-sm"
              disabled={locked || active === project.entry}
              title={
                active === project.entry
                  ? 'Choose another entry module before deleting this file'
                  : 'Delete file'
              }
              aria-label="Delete file"
              onClick={() => setDeleting(true)}
            >
              <Trash2 />
            </Button>
          </div>
          <div className="project-entry">
            <label htmlFor="entry-module">Entry module</label>
            <NativeSelect
              id="entry-module"
              value={project.entry}
              disabled={locked}
              onChange={(event) =>
                accept({ ...project, entry: event.target.value })
              }
            >
              {project.order.map((path) => (
                <NativeSelectOption key={path} value={path}>
                  {path}
                </NativeSelectOption>
              ))}
            </NativeSelect>
            <small>Modules compile top to bottom.</small>
          </div>
        </CollapsibleContent>
        <div className="project-documents">
          {paths.map((path) => (
            <div
              key={path}
              className="project-document"
              hidden={path !== active}
            >
              <SourceEditor
                filename={path}
                source={project.files[path]}
                disabled={locked}
                onChange={(source) =>
                  onChange({
                    ...project,
                    files: { ...project.files, [path]: source },
                  })
                }
                onKeyDown={(event) => {
                  if (
                    (event.ctrlKey || event.metaKey) &&
                    event.key === 'Enter'
                  ) {
                    event.preventDefault();
                    if (!locked) onCompile();
                  }
                }}
              />
            </div>
          ))}
        </div>
      </div>
      {error && !dialog && (
        <p className="project-error" role="alert">
          {error}
        </p>
      )}
      <footer className="pane-status">
        <span>
          <span>Ur</span>
          <span>{project.files[active]?.split('\n').length ?? 0} lines</span>
          <span>2 spaces</span>
        </span>
        <span>Tab / Shift+Tab to indent</span>
      </footer>
      <p id="editor-keyboard-help" className="sr-only">
        Tab indents; Shift+Tab unindents. Enter carries indentation. Escape then
        Tab leaves the editor. Control or Command+Enter compiles the project.
      </p>
      <Dialog
        open={!!dialog}
        onOpenChange={(open) => {
          if (!open) setDialog(null);
        }}
      >
        <DialogContent className="project-dialog">
          <form
            onSubmit={(event) => {
              event.preventDefault();
              saveFilename();
            }}
          >
            <DialogHeader>
              <DialogTitle>
                {dialog === 'new' ? 'New file' : 'Rename file'}
              </DialogTitle>
              <DialogDescription>
                {dialog === 'new'
                  ? 'Add an .ur implementation, or an .urs signature for an existing module.'
                  : 'A matching signature is renamed with its implementation. Update module references in your source after renaming.'}
              </DialogDescription>
            </DialogHeader>
            <label htmlFor="filename">Filename</label>
            <Input
              id="filename"
              value={filename}
              onChange={(event) => setFilename(event.target.value)}
              placeholder="math.ur"
              autoComplete="off"
            />
            {error && (
              <p className="project-error" role="alert">
                {error}
              </p>
            )}
            <DialogFooter>
              <Button
                variant="outline"
                type="button"
                onClick={() => setDialog(null)}
              >
                Cancel
              </Button>
              <Button type="submit" disabled={locked}>
                {dialog === 'new' ? 'Create file' : 'Rename'}
              </Button>
            </DialogFooter>
          </form>
        </DialogContent>
      </Dialog>
      <AlertDialog open={deleting} onOpenChange={setDeleting}>
        <AlertDialogContent className="project-dialog">
          <AlertDialogHeader>
            <AlertDialogTitle>Delete {active}?</AlertDialogTitle>
            <AlertDialogDescription>
              This removes the file from this project. A matching signature is
              also removed when deleting its implementation. This cannot be
              undone.
            </AlertDialogDescription>
          </AlertDialogHeader>
          <AlertDialogFooter>
            <AlertDialogCancel>Cancel</AlertDialogCancel>
            <AlertDialogAction
              disabled={locked}
              onClick={() => {
                const files = { ...project.files };
                delete files[active];
                if (active.endsWith('.ur')) delete files[active + 's'];
                accept(
                  {
                    ...project,
                    files,
                    order: project.order.filter((path) => path !== active),
                  },
                  project.entry,
                );
                setDeleting(false);
              }}
            >
              Delete file
            </AlertDialogAction>
          </AlertDialogFooter>
        </AlertDialogContent>
      </AlertDialog>
    </Collapsible>
  );
}
